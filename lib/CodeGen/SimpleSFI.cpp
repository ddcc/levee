//===-- SimpleSFI.cpp - Simple SFI implementation for CPI -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass instruments all memory accesses in a program to ensure they
// won't be able to access the CPI/CPS safe retion.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "simple-sfi"
#include "llvm/Support/Debug.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/DenseSet.h"

using namespace llvm;

namespace llvm {

cl::opt<bool> ShowSimpleSFIStats("simple-sfi-stats",
      cl::desc("Show simple sfi compile-time statistics"),
      cl::init(false));

STATISTIC(NumLoads, "Total number of loads");
STATISTIC(NumStores, "Total number of stores");
STATISTIC(NumMasksInserted, "Total number of masking operations inserted");

} // namespace llvm

namespace {
  class SimpleSFI : public FunctionPass {
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DataLayout>();
    }

    virtual bool runOnFunction(Function &F);
    virtual bool doFinalization(Module &);

  public:
    static char ID; // Pass identification, replacement for typeid.
    SimpleSFI(): FunctionPass(ID) {
      initializeSafeStackInserterPass(*PassRegistry::getPassRegistry());
    }
  };
} // end anonymous namespace

char SimpleSFI::ID = 0;
INITIALIZE_PASS(SimpleSFI, "simple-sfi",
                "Simple SFI instrumentation pass", false, false)

Pass *llvm::createSimpleSFIPass() {
  return new SimpleSFI();
}

bool SimpleSFI::runOnFunction(Function &F) {
  if (!F.hasFnAttribute("has-cpi") && !F.hasFnAttribute("has-cps"))
    return false;

  bool Changed = false;
  DataLayout* DL = &getAnalysis<DataLayout>();
  Type *IntPtrTy = DL->getIntPtrType(F.getContext());

  // Keep track of what addresses are already masked
  llvm::DenseSet<Value*> MaskedPointers;

  // Traverse the function in a topological sort order
  ReversePostOrderTraversal<Function*> RPOT(&F);
  for (ReversePostOrderTraversal<Function*>::rpo_iterator I = RPOT.begin(),
         E = RPOT.end(); I != E; ++I) {
    BasicBlock *BB = *I;

    for (BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
      if (isa<LoadInst>(&*I)) {
        ++NumLoads;
        continue;
      }

      StoreInst *SI = dyn_cast<StoreInst>(&*I);
      if (!SI) // We only instrument store instructions
        continue;

      ++NumStores;

      Value *Ptr = SI->getPointerOperand();

      if (SI->getPointerAddressSpace() != 0)
          // For now, we assume that all store instructions to non-0 address spaces
          // are either CPI-protected, or access address spaces that are disjoint with
          // the main memory anyway.
        continue;

      // Traverse the data flow upwards through constant GEPs, casts, etc.,
      // in order to maximize the chance of reusing the mask operations
      // across different stores.
      while (Ptr && isa<Instruction>(Ptr) && Ptr->getType()->isPointerTy()) {
        if (isa<AllocaInst>(Ptr)) {
          // Do not instrument accesses to the safe stack
          Ptr = 0;
        } else if (MaskedPointers.count(Ptr)) {
          // This pointer is already masked
          Ptr = 0;
        } else if (CastInst *CI = dyn_cast<CastInst>(Ptr)) {
          Ptr = CI->getOperand(0);
        } else if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
          if (!GEP->hasAllConstantIndices())
            break; // Mask the result of non-constant GEPs
          Ptr = GEP->getPointerOperand();
        } else {
          break;
        }
      }

      if (!Ptr || isa<Constant>(Ptr))
        continue;

      // Find a suitable insertion point
      Instruction *InsertPt;
      if (isa<Instruction>(Ptr)) {
        InsertPt = cast<Instruction>(Ptr)->getNextNode();
      } else if (isa<Argument>(Ptr)) {
        InsertPt = F.getEntryBlock().getFirstNonPHIOrDbgOrLifetime();
      } else {
        llvm_unreachable(
              "A pointer must be either instruction or constant or argument.");
      }

      while (isa<AllocaInst>(InsertPt) || isa<PHINode>(InsertPt))
        InsertPt = InsertPt->getNextNode();

      IRBuilder<> IRB(InsertPt);

      // We create the masking operation using undef value at first, so
      // that we can use replaceAllUsesWith on Ptr alter.

      Instruction *FirstInst;
      Value *MaskedPtr = UndefValue::get(Ptr->getType());

      MaskedPtr = FirstInst = IRB.Insert(
            CastInst::Create(Instruction::PtrToInt, MaskedPtr, IntPtrTy));

      MaskedPtr = IRB.CreateAnd(MaskedPtr, IRB.getInt64((1ull<<46) - 1));
      MaskedPtr = IRB.CreateIntToPtr(MaskedPtr, Ptr->getType(),
                                     Twine("masked.") + Ptr->getName());
      Ptr->replaceAllUsesWith(MaskedPtr);
      FirstInst->setOperand(0, Ptr);

      MaskedPointers.insert(MaskedPtr);
      ++NumMasksInserted;
      Changed = true;
    }
  }
  return Changed;
}

static void PrintStat(raw_ostream &OS, Statistic &S) {
  OS << format("%8u %s - %s\n", S.getValue(), S.getName(), S.getDesc());
}

bool SimpleSFI::doFinalization(Module &) {
  if (ShowSimpleSFIStats) {
    outs() << "SimpleSFI Compilation Statistics:\n";

    PrintStat(outs(), NumLoads);
    PrintStat(outs(), NumStores);
    PrintStat(outs(), NumMasksInserted);
  }

  return false;
}