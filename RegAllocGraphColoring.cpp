#define DEBUG_TYPE "regalloc"
#include "RenderMachineFunction.h"
#include "llvm/Function.h"
#include "VirtRegRewriter.h"
#include "VirtRegMap.h"
#include "Spiller.h"
#include "llvm/CodeGen/RegisterCoalescer.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Target/TargetInstrInfo.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Compiler.h"
#include <algorithm>
#include <set>
#include <map>
#include <queue>
#include <memory>
#include <cmath>

using namespace llvm;
using namespace std;

static RegisterRegAlloc
GraphColorRegAlloc("color1", "graph coloring register allocator",
            createColorRegisterAllocator);

namespace {
	map<unsigned, set<unsigned> > InterferenceGraph;
	map<unsigned, int> Degree;
   	map<unsigned, bool> OnStack;
	set<unsigned> Colored;
	BitVector Allocatable;
	set<unsigned> PhysicalRegisters;

	class RegAllocGraphColoring : public MachineFunctionPass 
	{
		public:
			static char ID;

			LiveIntervals *LI;
			MachineFunction *MF;
			const TargetMachine *TM;
			const TargetRegisterInfo *TRI;
  			const MachineLoopInfo *loopInfo;
  			const TargetInstrInfo *tii;
  			MachineRegisterInfo *mri;
			RenderMachineFunction *rmf;

			VirtRegMap *vrm;
			LiveStacks *lss;
			int k;

			RegAllocGraphColoring() : MachineFunctionPass(ID)
			{
				initializeSlotIndexesPass(*PassRegistry::getPassRegistry());
				initializeLiveIntervalsPass(*PassRegistry::getPassRegistry());
				initializeRegisterCoalescerAnalysisGroup(*PassRegistry::getPassRegistry());
				initializeLiveStacksPass(*PassRegistry::getPassRegistry());
				initializeMachineLoopInfoPass(*PassRegistry::getPassRegistry());
				initializeVirtRegMapPass(*PassRegistry::getPassRegistry());
				initializeRenderMachineFunctionPass(*PassRegistry::getPassRegistry());
				initializeStrongPHIEliminationPass(*PassRegistry::getPassRegistry());
			}

			virtual const char *getPassName() const
			{
				return "Graph Coloring Register Allocator";
			}
			virtual void getAnalysisUsage(AnalysisUsage &AU) const 
			{
				AU.addRequired<SlotIndexes>();
				AU.addPreserved<SlotIndexes>();
				AU.addRequired<LiveIntervals>();
  				AU.addRequired<RegisterCoalescer>();
				AU.addRequired<LiveStacks>();
				AU.addPreserved<LiveStacks>();
				AU.addRequired<MachineLoopInfo>();
				AU.addPreserved<MachineLoopInfo>();
				AU.addRequired<RenderMachineFunction>();
				if(StrongPHIElim)
					AU.addRequiredID(StrongPHIEliminationID);
				AU.addRequired<VirtRegMap>();
				MachineFunctionPass::getAnalysisUsage(AU);
			}

			bool runOnMachineFunction(MachineFunction &Fn);
			void buildInterferenceGraph();
			bool compatible_class(MachineFunction & mf, unsigned v_reg, unsigned p_reg);
			bool aliasCheck(unsigned preg, unsigned vreg);
			set<unsigned> getSetofPotentialRegs(TargetRegisterClass trc,unsigned v_reg);
			unsigned GetReg(set<unsigned> PotentialRegs, unsigned v_reg);
			bool colorNode(unsigned v_reg);
			bool allocateRegisters();
			bool SpillIt(unsigned v_reg);
			void addStackInterval(const LiveInterval*,MachineRegisterInfo *);
			void dumpPass();
	};
	char RegAllocGraphColoring::ID = 0;
}

//Builds Interference Graph
void RegAllocGraphColoring::buildInterferenceGraph()
{
	int num=0;
	for (LiveIntervals::iterator ii = LI->begin(); ii != LI->end(); ii++) 
	{
		
		if(TRI->isPhysicalRegister(ii->first))
			continue;
		num++;
		OnStack[ii->first] = false;    
		InterferenceGraph[ii->first].insert(0);
		const LiveInterval *li = ii->second;
		for (LiveIntervals::iterator jj = LI->begin(); jj != LI->end(); jj++) 
		{
			const LiveInterval *li2 = jj->second;
			if(jj->first == ii->first)
				continue;
			if(TRI->isPhysicalRegister(jj->first))
				continue;
			if (li->overlaps(*li2)) 
			{
				if(!InterferenceGraph[ii->first].count(jj->first))
				{
					InterferenceGraph[ii->first].insert(jj->first);
					Degree[ii->first]++;
				}
				if(!InterferenceGraph[jj->first].count(ii->first))
				{
					InterferenceGraph[jj->first].insert(ii->first);
					Degree[jj->first]++;
				}
			}
		}	
	}
	errs( )<<"\nVirtual registers: "<<num;
}

//This function is used to check the compatibility of virtual register with the physical reg.
//For Eg. floating point values must be stored in floating point registers.
bool RegAllocGraphColoring::compatible_class(MachineFunction & mf, unsigned v_reg, unsigned p_reg)
{
	assert(MRegisterInfo::isPhysicalRegister(p_reg) &&
			"Target register must be physical");
	const TargetRegisterClass *trc = mf.getRegInfo().getRegClass(v_reg);

	return trc->contains(p_reg);
}

//check if aliases are empty
bool RegAllocGraphColoring::aliasCheck(unsigned preg, unsigned vreg)
{
	const unsigned *aliasItr = TRI->getAliasSet(preg);
	while(*aliasItr != 0)
	{
		for(set<unsigned>::iterator ii = InterferenceGraph[vreg].begin( );
				ii != InterferenceGraph[vreg].end( ); ii++)
		{
			if(Colored.count( *ii ) && vrm->getPhys(*ii) == *aliasItr)
				return false;
		}
		aliasItr++;
	}
	return true;
}

//return the set of potential register for a virtual register
set<unsigned> RegAllocGraphColoring::getSetofPotentialRegs(TargetRegisterClass trc,unsigned v_reg)
{
	TargetRegisterClass::iterator ii;
	TargetRegisterClass::iterator ee;
	unsigned p_reg = vrm->getRegAllocPref(v_reg);
	if(p_reg != 0)
	{
		PhysicalRegisters.insert( p_reg );
	}
	else
	{
		ii = trc.allocation_order_begin(*MF);
		ee = trc.allocation_order_end(*MF);
		while(ii != ee)
		{
			PhysicalRegisters.insert( *ii );
			ii++;
		}
	}
	k = PhysicalRegisters.size();
	return PhysicalRegisters;
}

//returns the physical register to which the virtual register must be mapped. If there is no
//physical register available this function returns 0.
unsigned RegAllocGraphColoring::GetReg(set<unsigned> PotentialRegs, unsigned v_reg)
{
	for(set<unsigned>::iterator ii = PotentialRegs.begin( ); ii != PotentialRegs.end( ); ii++)
	{
		if(!LI->hasInterval(*ii) || !LI->hasInterval(v_reg))
		{
			continue;
		}
		LiveInterval li1 = LI->getInterval(*ii);
		LiveInterval li2 = LI->getInterval(v_reg);
		if( aliasCheck(*ii,v_reg) && !li1.overlaps(li2)&& compatible_class(*MF,v_reg,*ii))
		{
			return *ii;
		}
	}
	return 0;
}

// Adds a stack interval if the given live interval has been
// spilled. Used to support stack slot coloring.
void RegAllocGraphColoring::addStackInterval(const LiveInterval *spilled,
                                    MachineRegisterInfo* mri)
{
	int stackSlot = vrm->getStackSlot(spilled->reg);

	if (stackSlot == VirtRegMap::NO_STACK_SLOT)
	{
		return;
	}

	const TargetRegisterClass *RC = mri->getRegClass(spilled->reg);
	LiveInterval &stackInterval = lss->getOrCreateInterval(stackSlot, RC);

	VNInfo *vni;
	if (stackInterval.getNumValNums() != 0)
	{
		vni = stackInterval.getValNumInfo(0);
	} 
	else
 	{
		vni = stackInterval.getNextValue(
		SlotIndex(), 0, lss->getVNInfoAllocator());
	}

	LiveInterval &rhsInterval = LI->getInterval(spilled->reg);
	stackInterval.MergeRangesInAsValue(rhsInterval, vni);
}

//Spills virtual register
bool RegAllocGraphColoring::SpillIt(unsigned v_reg)
{

	const LiveInterval* spillInterval = &LI->getInterval(v_reg);
	SmallVector<LiveInterval*, 8> spillIs;
	rmf->rememberUseDefs(spillInterval);
	std::vector<LiveInterval*> newSpills =
		LI->addIntervalsForSpills(*spillInterval, spillIs, loopInfo, *vrm);
	addStackInterval(spillInterval, mri);
	rmf->rememberSpills(spillInterval, newSpills);
	return newSpills.empty();
}

//assigns physical to virtual register
bool RegAllocGraphColoring::colorNode(unsigned v_reg)
{
	bool notspilled = true;
	errs()<<"\nColoring Register  : "<<v_reg;
	unsigned p_reg = 0;
	const TargetRegisterClass *trc = MF->getRegInfo().getRegClass(v_reg);
	set<unsigned> PotentialRegs = getSetofPotentialRegs(*trc,v_reg);
	for(set<unsigned>::iterator ii = InterferenceGraph[v_reg].begin( ) ;
			ii != InterferenceGraph[v_reg].end( ); ii++)
	{
		if(Colored.count( *ii ))
			PotentialRegs.erase(vrm->getPhys(*ii));	
		if(PotentialRegs.empty( ))
			break;

	}
	//There are no Potential Physical Registers Available
	if(PotentialRegs.empty( ))
	{
		notspilled = SpillIt(v_reg);
		errs( )<<"\nVreg : "<<v_reg<<" ---> Spilled";
	}
	else
	{
		//Get compatible Physical Register
		p_reg = GetReg(PotentialRegs,v_reg);
		assert(p_reg!=0 && "Assigning 0 reg");
		//if no such register found due to interfernce with p_reg
		if(!p_reg)
		{
			notspilled = SpillIt(v_reg);
			errs( )<<"\nVreg : "<<v_reg<<" ---> Spilled";
		}
		else
		{
			//assigning virtual to physical register
			vrm->assignVirt2Phys( v_reg , p_reg );
			errs( )<<"\nVreg : "<<v_reg<<" ---> Preg :"<<TRI->getName(p_reg);
			Colored.insert(v_reg);
		}
	}
	return notspilled;
}

//This is the main graph coloring algorithm
bool RegAllocGraphColoring::allocateRegisters()
{
	bool round;
	unsigned min = 0;
	//find virtual register with minimum degree
	for(map<unsigned, set<unsigned> >::iterator ii = InterferenceGraph.begin(); ii != InterferenceGraph.end(); ii++)
	{
		if(!OnStack[ii->first] && (min == 0 || Degree[ii->first] < Degree[min]))
			min = ii->first;
	}		
	//if graph empty
	if(min == 0)
		return true;
	errs()<<"\nRegister selected to push on stack = "<<min;

	//push register onto stack
	OnStack[min] = true;

	//delete register from graph
	for(map<unsigned, set<unsigned> >::iterator ii = InterferenceGraph.begin(); ii != InterferenceGraph.end(); ii++)
	{
		if(ii->second.count(min))
			Degree[ii->first]--;
	}

	//recursive call
	round = allocateRegisters();

	//pop and color virtual register
	return colorNode(min) && round;
}


void RegAllocGraphColoring::dumpPass( )
{
	for (MachineFunction::iterator mbbItr = MF->begin(), mbbEnd = MF->end();
			mbbItr != mbbEnd; ++mbbItr) 
	{
		MachineBasicBlock &mbb = *mbbItr;
		errs() << "bb" << mbb.getNumber() << ":\n";
		for (MachineBasicBlock::iterator miItr = mbb.begin(), miEnd = mbb.end();
				miItr != miEnd; ++miItr) 
		{
			MachineInstr &mi = *miItr;
			errs( )<<mi;
		}
	}
}


bool RegAllocGraphColoring::runOnMachineFunction(MachineFunction &mf) 
{
	errs()<<"\nRunning On function: "<<mf.getFunction()->getName();
	MF = &mf;
	mri = &MF->getRegInfo(); 
	TM = &MF->getTarget();
	TRI = TM->getRegisterInfo();
	tii = TM->getInstrInfo();

	vrm = &getAnalysis<VirtRegMap>();
	LI = &getAnalysis<LiveIntervals>();
	lss = &getAnalysis<LiveStacks>();
	rmf = &getAnalysis<RenderMachineFunction>();
	loopInfo = &getAnalysis<MachineLoopInfo>();

	bool another_round = false;
	int round = 1;

	errs()<<"Pass before allocation\n";
	dumpPass();

	do
	{
		errs( )<<"\nRound #"<<round<<'\n';
		round++;
		vrm->clearAllVirt();
		buildInterferenceGraph();
		another_round = allocateRegisters();
		InterferenceGraph.clear( );
		Degree.clear( );
		OnStack.clear( );
		Colored.clear();
		Allocatable.clear();
		PhysicalRegisters.clear();
		errs( )<<*vrm;
	} while(!another_round);

	rmf->renderMachineFunction( "After GraphColoring Register Allocator" , vrm );

	std::auto_ptr<VirtRegRewriter> rewriter(createVirtRegRewriter());

	//this is used to write the final code.
	rewriter->runOnMachineFunction(*MF, *vrm, LI);

	errs()<<"Pass after allocation\n";
	dumpPass();

	vrm->dump( );

	return true;
}


FunctionPass *llvm::createColorRegisterAllocator() 
{
	return new RegAllocGraphColoring();
}
