#define DEBUG_TYPE "promote"
#include <llvm/Pass.h>
#include <llvm/Function.h>
#include <llvm/Support/InstIterator.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Instructions.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/CodeGen/MachineRegisterInfo.h>
#include "llvm/Transforms/Utils/SSAUpdater.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Analysis/Dominators.h"

using namespace llvm;
using namespace std;

STATISTIC(NumLoadsHoisted, "Number of loads hoisted");
STATISTIC(NumStoresSunked, "Number of stores sunked");

namespace {
	struct RegPromotion : public FunctionPass
	{	
		static char ID;
		RegPromotion() : FunctionPass(ID){}
		virtual bool runOnFunction(Function &F);
		virtual void getAnalysisUsage(AnalysisUsage &AU) const;	
		void getSubLoops(Loop *L);
		void promoteAllLoops();
		void promoteInLoop(Loop *L);
		bool findLoadsAndStoresAdded(Loop* L);	
		void insertLoads();		
		void replaceLoadsByCopies(Loop* L);
		void insertStores();
		void deleteDeadStores();
		void deleteDeadLoads();	
		void computeIN(BasicBlock*);
		void computeOUT(BasicBlock*);
		void insertPhi(BasicBlock*);
		void clear();			

		set<pair<Value*, Instruction*> > LoadsAdded;
		set<pair<Value*, Instruction*> > StoresAdded;
		set<Instruction*> NewInstructionsAdded;
		map<BasicBlock*, map<Value*, PHINode*> > NewPhiInstructionsAdded;
		map<Instruction*, Value*> Replace;
		map<Value*, set<User*> > ReplaceBy;
		set<Instruction*> deadStores;
		set<Instruction*> deadLoads;
		map<BasicBlock*, map<Value*, set<Value*> > > IN_BBVRMap, OUT_BBVRMap;
		map<BasicBlock*, map<Value*, set<BasicBlock*> > > ComesFrom;
		map<BasicBlock*, bool> Change;
		set<Value*> MemoryObjects;
		map<Value*, unsigned> Alignment;
		LoopInfo *LI;
	};

	char RegPromotion::ID = 0;
	static RegisterPass<RegPromotion> tmp("promote", "promotes loads and stores", false, false);
}

//finds loads and stores to be added
bool RegPromotion::findLoadsAndStoresAdded(Loop *L)
{
	//load to be inserted in loop preheader
	Instruction* insertLoadBefore = L->getLoopPreheader()->getTerminator(),*preheader;
	preheader = insertLoadBefore;

	//stores to be inserted in all exit blocks of loop
	SmallVectorImpl<BasicBlock*> insertStoreInBlocks(0);
	L->getUniqueExitBlocks(insertStoreInBlocks);
	vector<Instruction*> insertStoreBefore;
	for(SmallVectorImpl<BasicBlock*>::iterator i = insertStoreInBlocks.begin(); i != insertStoreInBlocks.end(); i++)
		insertStoreBefore.push_back((*i)->begin());

	//forward scan for loads
	for(Loop::block_iterator i = L->block_begin(); i != L->block_end(); i++)
	{
		for(BasicBlock::iterator j = (*i)->begin(); j != (*i)->end(); j++)
		{
			if(isa<CallInst>(j) || (isa<LoadInst>(j) && (!isa<GlobalVariable>(j->getOperand(0)) && !isa<GetElementPtrInst>(j->getOperand(0))))){
				return false;
			}
			else if(isa<LoadInst>(j) && !(dyn_cast<LoadInst>(j)->isVolatile()))
			{
				if(!isa<GetElementPtrInst>(j->getOperand(0))){
					LoadsAdded.insert(pair<Value*, Instruction*>(j->getOperand(0), insertLoadBefore));	
					MemoryObjects.insert(j->getOperand(0));
					Alignment[j->getOperand(0)] = dyn_cast<LoadInst>(j)->getAlignment();
					deadLoads.insert(j);
				}
			}
		}

		for(BasicBlock::iterator j = (*i)->begin(); j != (*i)->end(); j++)
		{
			if(isa<CallInst>(j) || (isa<StoreInst>(j) && !isa<GlobalVariable>(j->getOperand(1))&& !isa<GetElementPtrInst>(j->getOperand(1))))
				return false;
			if(isa<StoreInst>(j) && !(dyn_cast<StoreInst>(j)->isVolatile()))
			{
				if(!isa<GetElementPtrInst>(j->getOperand(1))){
					for(vector<Instruction*>::iterator i = insertStoreBefore.begin(); i != insertStoreBefore.end(); i++)
					{
						StoresAdded.insert(pair<Value*, Instruction*>(j->getOperand(1), *i));
					}
					if(MemoryObjects.count(j->getOperand(1)) == 0){
						LoadsAdded.insert(pair<Value*, Instruction*>(j->getOperand(1), preheader));
						MemoryObjects.insert(j->getOperand(1));
						Alignment[j->getOperand(1)] = (dyn_cast<StoreInst>(j))->getAlignment();
					}
                    deadStores.insert(j);
                }
            }
        }

	}

	NumStoresSunked += StoresAdded.size();
	return true;
}

//inserts loads from loads added set
void RegPromotion::insertLoads()
{
	LoadInst *loadInst;
	for(set<pair<Value*, Instruction*> >::iterator i = LoadsAdded.begin(); i != LoadsAdded.end(); i++)
	{
		loadInst = new LoadInst(i->first, i->first->getName(), i->second);
		loadInst->setAlignment(Alignment[i->first]);
		NewInstructionsAdded.insert(loadInst);
	}
}


//inserts phi instructions in basic block if IN<memory operand> has multiple values
//create new phi or replace if it already exists
void RegPromotion::insertPhi(BasicBlock* BB)
{
  Value *v;
  for(set<Value*>::iterator si = MemoryObjects.begin(); si != MemoryObjects.end(); si++)
  {
	v = *si;
	if(IN_BBVRMap[BB][v].size() > 1)
	{
	  //replace if exists:-
	  if(NewPhiInstructionsAdded[BB].count(v))
	  {
		PHINode* phi = NewPhiInstructionsAdded[BB][v];
		for(set<Value*>::iterator si = IN_BBVRMap[BB][v].begin(); si != IN_BBVRMap[BB][v].end(); si++ )
		{
		  for(set<BasicBlock*>::iterator bi = ComesFrom[BB][*si].begin(); bi != ComesFrom[BB][*si].end(); bi++)
		  {
			if(phi->getIncomingValueForBlock(*bi) != *si)
			{
			  if(phi->getBasicBlockIndex(*bi) != -1)
			  {
				phi->removeIncomingValue(*bi, false);
				phi->addIncoming(*si, *bi);
			  }
			  else
				phi->addIncoming(*si, *bi);
			}
		  }
		}
		OUT_BBVRMap[BB][v].clear();
		OUT_BBVRMap[BB][v].insert(phi);
	  }
	  else
	  {
		//create new:-
		Twine name = v->getName();
		Instruction *insertBefore = BB->begin();
		PHINode *phi = PHINode::Create((*IN_BBVRMap[BB][v].begin())->getType(), name, insertBefore);
		//set incoming values:
		for(set<Value*>::iterator si = IN_BBVRMap[BB][v].begin(); si != IN_BBVRMap[BB][v].end(); si++ )
		  for(set<BasicBlock*>::iterator bi = ComesFrom[BB][*si].begin(); bi != ComesFrom[BB][*si].end(); bi++)
		  {
			if(phi->getBasicBlockIndex(*bi) != -1)
			{
			  phi->removeIncomingValue(*bi, false);
			  phi->addIncoming(*si, *bi);
			}
			else
			  phi->addIncoming(*si, *bi);
		  }
		NewPhiInstructionsAdded[BB][v] = phi;
		//kill
		OUT_BBVRMap[BB][v].clear();
		//gen
		OUT_BBVRMap[BB][v].insert(phi);
	  }
	}
  }
}

//computes IN(BasicBlock) = union(OUT(predecessors of the basic block))
void RegPromotion::computeIN(BasicBlock* BB)
{
	Value *v;
	set<Value*> unionSet;
	Change[BB] = false;
	ComesFrom[BB].clear();

	//for each memory operand
	for(set<Value*>::iterator si = MemoryObjects.begin(); si != MemoryObjects.end(); si++)
	{
		v = *si;
		unionSet.clear();
		//for each predecessor
		for(pred_iterator pi = pred_begin(BB); pi != pred_end(BB); ++pi)
		{

			for(set<Value*>::iterator i = OUT_BBVRMap[*pi][v].begin(); i != OUT_BBVRMap[*pi][v].end(); i++)
			{
				unionSet.insert(*i);
				ComesFrom[BB][*i].insert(*pi);
			}
		}
		//if IN of basic block has changed
		if(unionSet != IN_BBVRMap[BB][v])
		{
			Change[BB] = true;
			IN_BBVRMap[BB][v] = OUT_BBVRMap[BB][v] = unionSet;
		}
	}


}

//computes OUT of basic block, inserts stores, and replaces loads by copies
void RegPromotion::computeOUT(BasicBlock* BB)
{
  Instruction *I;
  Value* v;

  //insert phi instructions
  insertPhi(BB);

  //iterate through instructions to compute OUT
  for(BasicBlock::iterator j = BB->begin(); j != BB->end(); j++)
  {
	I = j;
	//insert new stores 
	for(set<pair<Value*, Instruction*> >::iterator si = StoresAdded.begin(); si != StoresAdded.end(); si++)
	{
	  if(si->second == I)
	  {
		Value *v = *(OUT_BBVRMap[BB][si->first].begin());
		if(!v)
		  continue;
		StoreInst *st = new StoreInst(v, si->first,I);//how does one decide alignment?
		st->setAlignment(Alignment[v]);
		NewInstructionsAdded.insert(st);
		StoresAdded.erase(si);
	  }
	}

	//new load: kill and gen
	if(isa<LoadInst>(I) && NewInstructionsAdded.count(I))
	{
	  //kill
	  OUT_BBVRMap[BB][I->getOperand(0)].clear();
	  //gen
	  OUT_BBVRMap[BB][I->getOperand(0)].insert(I);
	}

	//new store: replace
	else if(isa<StoreInst>(I) && NewInstructionsAdded.count(I))
	{
	  //create new new store
	  Value *v = *(OUT_BBVRMap[BB][I->getOperand(1)].begin());
	  if(!v)
		continue;
	  StoreInst *st = new StoreInst(v, I->getOperand(1), I);
	  NewInstructionsAdded.insert(st);
	  j--;//points to new new store
	  //delete old new store
	  I->eraseFromParent();
	}

	//old store: kill and gen
	else if(isa<StoreInst>(I) && deadStores.count(I))
	{
	  //kill
	  OUT_BBVRMap[BB][I->getOperand(1)].clear();
	  //gen
	  OUT_BBVRMap[BB][I->getOperand(1)].insert(I->getOperand(0));
	}

	//old load:replace by copy
	else if(isa<LoadInst>(I) && deadLoads.count(I))
	{

	  //replace all uses of previous register by new register
	  v = *(OUT_BBVRMap[BB][I->getOperand(0)].begin());
	  if(!v)
		continue;

	  if(ReplaceBy.count(I) == 0)
	  {
		//insert all uses of value
		for(value_use_iterator<User> i = I->use_begin(); i != I->use_end(); i++)
		{
		  ReplaceBy[I].insert(*i);
		}
		Replace[I] = I;
	  }
	  for(set<User*>::iterator i = ReplaceBy[I].begin(); i != ReplaceBy[I].end(); i++)
	  {
		//replace all uses
		(*i)->replaceUsesOfWith(Replace[I], v);
		if(MemoryObjects.count( Replace[I] )!=0){
		  MemoryObjects.erase( Replace[I] );
		  MemoryObjects.insert(v);
		  Value *temp;
		  temp = *(OUT_BBVRMap[BB][Replace[I]].begin());
		  OUT_BBVRMap[BB].erase(Replace[I]);
		  OUT_BBVRMap[BB][v].insert(temp);
		}

	  }
	  Replace[I] = v;

	}
  }

}

//replaces loads within the loop by copies, and much more...
void RegPromotion::replaceLoadsByCopies(Loop* L)
{
  BasicBlock *BB;
  bool change = true;

  //preheader
  BB = L->getLoopPreheader();
  computeIN(BB);
  computeOUT(BB);

  while(change)
  {
	change = false;

	//scan all blocks
	for(Loop::block_iterator i = L->block_begin(); i != L->block_end(); i++)
	{
		BB = *i;
		computeIN(BB);

		if(Change[BB])
		{
			change = true;
			computeOUT(BB);
		}

	}
  }

  //tail: insert stores
  SmallVectorImpl<BasicBlock*> tailBlocks(0);
  L->getUniqueExitBlocks(tailBlocks);
  for(SmallVectorImpl<BasicBlock*>::iterator i = tailBlocks.begin(); i != tailBlocks.end(); i++)
  {
	BB = *i;
	computeIN(BB);
	computeOUT(BB);
  }
}

//deletes dead loads from loop
void RegPromotion::deleteDeadLoads()
{
  for(set<Instruction*>::iterator i = deadLoads.begin(); i != deadLoads.end(); i++)
  {
	(*i)->eraseFromParent();
  }
  NumLoadsHoisted += LoadsAdded.size();
}

//deletes dead stores from loop
void RegPromotion::deleteDeadStores()
{
  for(set<Instruction*>::iterator i = deadStores.begin(); i != deadStores.end(); i++)
  {
	(*i)->eraseFromParent();
  }
}

//clears all datastructures
void RegPromotion::clear()
{
  IN_BBVRMap.clear();
  OUT_BBVRMap.clear();
  deadStores.clear();
  deadLoads.clear();
  LoadsAdded.clear();
  StoresAdded.clear();
  Replace.clear();
  ReplaceBy.clear();
  NewInstructionsAdded.clear();
  NewPhiInstructionsAdded.clear();
  ComesFrom.clear();
  Change.clear();
}

//promotes loads and stores within a loop
void RegPromotion::promoteInLoop(Loop* L)
{
  bool promotable = findLoadsAndStoresAdded(L);
  if(promotable){
	errs()<<"Pass executed\n";
	insertLoads();
	replaceLoadsByCopies(L);
	deleteDeadLoads();
	deleteDeadStores();
	clear();
  }
  else{
	errs()<<"Pass not executed\n";
  }
}

//finds children of a loop
void RegPromotion::getSubLoops(Loop *L)
{
	vector<Loop*> sub = L->getSubLoops();
	for(vector<Loop*>::iterator i = sub.begin(); i != sub.end(); i++)
	{
		getSubLoops(*i);
	}
	promoteInLoop(L);
}

//finds all top level loops
void RegPromotion::promoteAllLoops()
{
  for(LoopInfo::iterator i = LI->begin(); i != LI->end(); i++)
  {
	getSubLoops(*i);
  }
}

void callMem2reg(Function &F,DominatorTree &DT)
{
  std::vector<AllocaInst*> Allocas;

  BasicBlock &BB = F.getEntryBlock();  // Get the entry node for the function

  while (1) {
	Allocas.clear();

	for (BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E; ++I)
	  if (AllocaInst *AI = dyn_cast<AllocaInst>(I))       // Is it an alloca?
		if (isAllocaPromotable(AI))
		  Allocas.push_back(AI);

	if (Allocas.empty()) break;

	PromoteMemToReg(Allocas, DT);
  }
}
bool RegPromotion::runOnFunction(Function &F)
{
  LI = &getAnalysis<LoopInfo>();
  DominatorTree &DT = getAnalysis<DominatorTree>();
  callMem2reg(F,DT);
  promoteAllLoops(); 
  return true;
}

void RegPromotion::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.setPreservesAll();
  AU.addRequired<LoopInfo>();
  AU.addRequired<DominatorTree>();
}

