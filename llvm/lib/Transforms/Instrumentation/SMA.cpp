#include <assert.h>
#include <stdio.h>

#include <iostream>
#include <map>
#include <vector>
#include <set>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/DiagnosticPrinter.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SpecialCaseList.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/Twine.h"

#include "SMA.h"

using namespace llvm;
using namespace std;

/*
 * Type decls.
 */
typedef vector<tuple<Instruction *, Value *, unsigned>> Plan;
typedef map<Value *, Value *> PtrInfo;
// PtrInfo boundInfo;

// vector<Function*> instrumented;
PtrInfo globalInfo;
PtrInfo calcBound;

// PtrInfo sizeInfo;
// vector<Value*> maskInfo;
// map<Value*, Type*> PtrTypeInfo;
// set<Instruction*> eraseInstInfo;
/*
 * A bounds object represents a range lb..ub.  As a simplification, the lower
 * bounds is always fixed to (0) since 99% of the time this is sufficient.
 */
struct Bounds
{
    static const int64_t NONFAT_BOUND  = INT64_MAX;
    static const int64_t UNKNOWN_BOUND = INT64_MIN;

    static const int64_t lb = 0;
    int64_t ub;

    Bounds() : ub(0)
    {

    }

    Bounds(size_t lb, size_t ub) : ub(ub)
    {
        if (lb != 0)
            ub = UNKNOWN_BOUND;
    }

    static Bounds empty()
    {
        return Bounds();
    }

    static Bounds nonFat()
    {
        return Bounds(0, NONFAT_BOUND);
    }

    static Bounds unknown()
    {
        return Bounds(0, UNKNOWN_BOUND);
    }

    bool isUnknown()
    {
        return (ub == UNKNOWN_BOUND);
    }

    bool isNonFat()
    {
        return (ub == NONFAT_BOUND);
    }

    bool isInBounds(int64_t k = 0)
    {
        return (k >= lb && k <= ub);
    }

    Bounds &operator-=(size_t k)
    {
        if (k == 0)
            return *this;
        if (isUnknown() || isNonFat())
            return *this;
        if (k > (size_t)ub)
            ub = UNKNOWN_BOUND;
        else
            ub -= (int64_t)k;
        return *this;
    }

    static Bounds min(Bounds bounds1, Bounds bounds2)
    {
        return Bounds(0, std::min(bounds1.ub, bounds2.ub));
    }
};

typedef map<Value *, Bounds> BoundsInfo;

/*
 * Prototypes.
 */
static Bounds getPtrBounds(const DataLayout *DL,
    Value *Ptr, BoundsInfo &boundsInfo);
static void getInterestingInsts(const TargetLibraryInfo *TL,
    const DataLayout *DL, BoundsInfo &boundsInfo, Instruction *I, Plan &plan);

static Value *calcBasePtr(Function *F, Value *Ptr);
static Value *calcBasePtr(Function *F,
    Value *Ptr, Instruction *I, PtrInfo &baseInfo);

static bool isInterestingAlloca(Instruction *I);

// static bool isInterestingGlobal(GlobalVariable *GV);
static bool isNoInstrument(Value *V);

static void insertBoundsCheck(const DataLayout *DL, Instruction *I, Value *Ptr,
    unsigned info, const PtrInfo &baseInfo);


/* 
 * Options
 */
static cl::opt<bool> option_debug("sma-debug",
    cl::desc("Print debug info when compiling"));

/*
 * Warning message class.
 */
class MinFatWarning : public DiagnosticInfo
{
    private:
        string msg;
    
    public:
        MinFatWarning(const char *msg) : DiagnosticInfo(777, DS_Warning),
            msg(msg) { }
        void print(DiagnosticPrinter &dp) const override;
};

void MinFatWarning::print(DiagnosticPrinter &dp) const
{
    dp << " [MinFat] Warning: " << msg << "\n";
}

static size_t clz(size_t value) {
    size_t res = 1;
    
    if (value == 0) {
        res = 64;
    }
    else {
        if ((value >> 32) == 0) { res += 32; value = value << 32; }
        if ((value >> 48) == 0) { res += 16; value = value << 16; }
        if ((value >> 56) == 0) { res += 8; value = value << 8; }
        if ((value >> 60) == 0) { res += 4; value = value << 4; }
        if ((value >> 62) == 0) { res += 2; value = value << 2; }
        res = res - (value >> 63);
    }
    return res;
}

// -------------------------------------------------------------------------

/*
 * Test if an integer value escapes or not.  If it does not, then there is no
 * point bounds checking pointer->integer casts.
 */
static bool doesIntEscape(Value *Val, set<Value *> &seen)
{
    if (seen.find(Val) != seen.end())
        return false;
    seen.insert(Val);

    // Sanity check:
    if (Val->getType()->isVoidTy())
    {
        errs() << *Val << "\n";
        Val->getContext().diagnose(MinFatWarning(
            "(BUG) unknown integer escape"));
        return true;
    }

    // bool ret = false;
    // bool used_as_union = false;
    for (User *User: Val->users())
    {
        if (isa<ReturnInst>(User) ||
                isa<CallInst>(User) ||
                isa<InvokeInst>(User) ||
                isa<StoreInst>(User))
            return true;
        if (isa<CmpInst>(User) ||
                isa<BranchInst>(User) ||
                isa<SwitchInst>(User))
            continue;
        if (doesIntEscape(User, seen))
            return true;
        // if (isa<IntToPtrInst>(User)) {
        //     return true;
        // }
    }

    return false;
}

enum AllocaEnum {isInteresting, notInteresting, usedAsUnion};
/*
 * Determine if the given alloca escapes (including if it is used in a bounds
 * check).  If it escapes then the alloca needs to be made non-fat.
 */
static AllocaEnum doesAllocaEscape(Value *Val, set<Value *> &seen)
{
    if (seen.find(Val) != seen.end()) {
        // return false;
        return notInteresting;
    }
    seen.insert(Val);

    // Sanity check:
    if (Val->getType()->isVoidTy())
    {
        errs() << *Val << "\n";
        Val->getContext().diagnose(MinFatWarning(
            "(BUG) unknown alloca escape"));
        // return true;
        return isInteresting;
    }

    AllocaEnum ret = notInteresting;
    bool used_as_union = false;
    bool is_interesting = false;
    for (User *User: Val->users())
    {
        if (isa<ReturnInst>(User))
        {
            // Return local variable = undefined; so does not count
            continue;
        }
        if (isa<LoadInst>(User) || isa<CmpInst>(User))
            continue;
        // if (StoreInst *Store = dyn_cast<StoreInst>(User))
        if (isa<StoreInst>(User))
        {
            // if (Store->getPointerOperand() == Val)
            //     continue;
            ret = isInteresting;
            is_interesting = true;
            continue;
        }
        if (isa<PtrToIntInst>(User))
        {
            set<Value *> seen;
            if (doesIntEscape(User, seen))
            {
                ret = isInteresting;
                is_interesting = true;
            }
            continue;
        }
        if (CallInst *Call = dyn_cast<CallInst>(User))  // Includes OOB-check
        {
            Function *F = Call->getCalledFunction();
            if (F != nullptr && F->doesNotAccessMemory())
                continue;
            ret = isInteresting;
            is_interesting = true;
            continue;
        }
        if (InvokeInst *Invoke = dyn_cast<InvokeInst>(User))
        {
            Function *F = Invoke->getCalledFunction();
            if (F != nullptr && F->doesNotAccessMemory())
                continue;
            ret = isInteresting;
            is_interesting = true;
            continue;
        }
        if (isa<GetElementPtrInst>(User) ||
            isa<SelectInst>(User) ||
            isa<PHINode>(User))
        {
            // if (doesAllocaEscape(User, seen))
            //     ret = true;
            ret = doesAllocaEscape(User, seen);
            if (ret == usedAsUnion)
                used_as_union = true;
            else if (ret == isInteresting)
                is_interesting = true;
            continue;
        }
        if (isa<BitCastInst>(User)) {
            BitCastInst *cast = dyn_cast<BitCastInst>(User);
            Type *Ty = cast->getDestTy();
            while (Ty->isPointerTy()) {
                Ty = Ty->getPointerElementType();
            }
            if (Ty->isStructTy()) {
                StringRef name = Ty->getStructName();
                if (name.startswith("union")) {
                    // errs() << "[Alloca]: found union usage" << name.str() << '\n';
                    // return false;
                    used_as_union = true;
                    continue;
                }
            }
            Ty = cast->getSrcTy();
            while (Ty->isPointerTy()) {
                Ty = Ty->getPointerElementType();
            }
            if (Ty->isStructTy()) {
                StringRef name = Ty->getStructName();
                if (name.startswith("union")) {
                    // errs() << "[Alloca]: " << *cast << '\n';
                    // return false;
                    used_as_union = true;
                    continue;
                }
            }
            ret = doesAllocaEscape(User, seen);
            if (ret == usedAsUnion)
                used_as_union = true;
            else if (ret == isInteresting)
                is_interesting = true;
            continue;
        }

        // if (Instruction *I = dyn_cast<Instruction>(User)) {
        //     // TODO: better way to distinguish our mask operation
        //     if (I->getOpcode() == Instruction::And) {
        //         printf(" [doesAllocaEscape]: this may be a mask instruction\n");
        //         User->dump();
        //         return true; // not sure
        //     }
        // }

        // Sanity check:
        errs() << *User << "\n";
        User->getContext().diagnose(MinFatWarning(
            "(BUG) unknown alloca user"));
        ret = isInteresting;
    }

    // return false;
    if (used_as_union)
        ret = usedAsUnion;
    else if (is_interesting)
        ret = isInteresting;
    return ret;
}

// -------------------------------------------------------------------------

/*
 * Determine if the given alloca is "interesting" or not.
 */
static bool isInterestingAlloca(Instruction *I)
{
    // if (option_no_replace_alloca)
    //     return false;
    AllocaInst *Alloca = dyn_cast<AllocaInst>(I);
    if (Alloca == nullptr)
        return false;
    set<Value *> seen;
    AllocaEnum ret = doesAllocaEscape(Alloca, seen);
    if (ret == isInteresting) {
        return true;
    }
    return false;
}

/*
 * Test if the given pointer is a memory allocation.  If so, then we know
 * that is pointer is already a base-pointer, so no need to call
 * lowfat_base().
 * TODO: I had planed to use TLI for this, but appears not to work correctly.
 */
static bool isMemoryAllocation(Value *Ptr)
{
    // if (option_no_replace_malloc)
    //     return false;
    Function *F = nullptr;
    if (CallInst *Call = dyn_cast<CallInst>(Ptr))
        F = Call->getCalledFunction();
    else if (InvokeInst *Invoke = dyn_cast<InvokeInst>(Ptr))
        F = Invoke->getCalledFunction();
    else
        return false;
    if (F == nullptr)
        return false;
    if (!F->hasName())
        return false;
    const string &Name = F->getName().str();
    if (Name == "malloc" || Name == "realloc" || Name == "_Znwm" ||
            Name == "_Znam" || Name == "_ZnwmRKSt9nothrow_t" ||
            Name == "_ZnamRKSt9nothrow_t" || Name == "calloc" ||
            Name == "valloc" || Name == "strdup" || Name == "strndup")
        return true;
    return false;
}

/*
 * Find the best place to insert instructions *after* `Ptr' is defined.
 */
static pair<BasicBlock *, BasicBlock::iterator> nextInsertPoint(Function *F,
    Value *Ptr)
{
    if (InvokeInst *Invoke = dyn_cast<InvokeInst>(Ptr))
    {
        // This is a tricky case since we an invoke instruction is also a
        // terminator.  Instead we create a new BasicBlock to insert into.
        BasicBlock *fromBB = Invoke->getParent();
        BasicBlock *toBB = Invoke->getNormalDest();
        BasicBlock *newBB = SplitEdge(fromBB, toBB);
        return make_pair(newBB, newBB->begin());
    }
    else if (isa<Argument>(Ptr) || isa<GlobalValue>(Ptr))
    {
        // For arguments or globals we insert into the entry basic block.
        BasicBlock &Entry = F->getEntryBlock();
        return make_pair(&Entry, Entry.begin());
    }
    else if (isa<Instruction>(Ptr) && !dyn_cast<Instruction>(Ptr)->isTerminator())
    {
        Instruction *I = dyn_cast<Instruction>(Ptr);
        assert(I != nullptr);
        BasicBlock::iterator i(I);
        i++;
        BasicBlock *BB = I->getParent();
        return make_pair(BB, i);
    }
    else
    {
        Ptr->getContext().diagnose(MinFatWarning(
            "(BUG) failed to calculate insert point"));
        BasicBlock &Entry = F->getEntryBlock();
        return make_pair(&Entry, Entry.begin());
    }
}

// -------------------------------------------------------------------------

/*
 * Insert an explicit lowfat_base(Ptr) operation after Ptr's origin.
 */
static Value *calcBasePtr(Function *F, Value *Ptr)
{
    auto i = nextInsertPoint(F, Ptr);
    IRBuilder<> builder(i.first, i.second);
    // Module *M = F->getParent();
    // Value *G = M->getOrInsertFunction("minfat_base",
    //     builder.getInt8PtrTy(),
    //     builder.getInt8PtrTy(),
    //     nullptr);
    // Ptr = builder.CreateBitCast(Ptr, builder.getInt8PtrTy());
    // Value *BasePtr = builder.CreateCall(G, {Ptr});

    Value *asInt = builder.CreatePtrToInt(Ptr, builder.getInt64Ty());
    Value *invertTag = builder.CreateAnd(asInt, MINFAT_TAG_MASK);
    Value *Tag = builder.CreateNot(invertTag);
    Tag = builder.CreateLShr(Tag, MINFAT_TAG_OFFSET);

    Value *Mask = builder.CreateShl(builder.getInt64(0xFFFFFFFFFFFFFFFF), Tag);
    Value *Size = builder.CreateShl(builder.getInt64(1), Tag);

    Value *BasePtr = builder.CreateAnd(asInt, Mask);
    Value *Bound = builder.CreateAdd(BasePtr, Size);
    BasePtr = builder.CreateIntToPtr(BasePtr, builder.getInt8PtrTy());

    calcBound.insert(make_pair(BasePtr, Bound));
    
    return BasePtr;
}

/*
 * Calculate the base pointer of a constant.
 */
static Value *calcBasePtr(Function *F,
    Constant *C, Instruction *I, PtrInfo &baseInfo)
{
    // if (option_no_replace_globals) {
    //     printf(" [ConstantPointerNull]: option_no_replace_globals\n");
    //     return ConstantPointerNull::get(Type::getInt8PtrTy(C->getContext()));
    // }
    Value *BasePtr = nullptr;

    auto i = baseInfo.find(C);
    if (i != baseInfo.end())
    {
        // Constant *R = dyn_cast<Constant>(i->second);
        // assert(R != nullptr);
        // return R;
        return i->second;
    }

    GlobalVariable *GV = dyn_cast<GlobalVariable>(C);
    if (GV != nullptr) {
        BasePtr = ConstantPointerNull::get(Type::getInt8PtrTy(C->getContext()));
        if (GV->hasName()) {
            StringRef Name = GV->getName();
            if (Name.startswith("tagged.")) {
                // shouldn't get here
                errs() << "[calcBasePtr]: (Constant) global starts with \"tagged.\" "
                       << *GV << '\n';
                abort();
            }
            auto k = globalInfo.find(GV);
            if (k != globalInfo.end()) {
                GlobalVariable *tagged = dyn_cast<GlobalVariable>(k->second);
                BasicBlock &entry = F->getEntryBlock();
                IRBuilder<> builder(&entry, entry.getFirstInsertionPt());
                BasePtr = builder.CreateLoad(tagged, tagged->getType());

                Value *AsInt = builder.CreatePtrToInt(BasePtr, builder.getInt64Ty());
                Value *InvertTag = builder.CreateAnd(AsInt, MINFAT_TAG_MASK);
                Value *Tag = builder.CreateNot(InvertTag);
                Tag = builder.CreateLShr(Tag, MINFAT_TAG_OFFSET);
                // Value *Mask = builder.CreateShl(builder.getInt64(0xFFFFFFFFFFFFFFFF), Tag);
                Value *Size = builder.CreateShl(builder.getInt64(1), Tag);

                Value *Bound = builder.CreateAdd(AsInt, Size);

                calcBound.insert(make_pair(BasePtr, Bound));
            }
            else {
                // not an interesting global, treat as non-fat
                BasePtr = ConstantPointerNull::get(Type::getInt8PtrTy(C->getContext()));
            }
        }
        else {
            // nameless global variable
            // BasePtr = ConstantExpr::getPointerCast(C,
            //         Type::getInt8PtrTy(C->getContext()));
            BasePtr = ConstantPointerNull::get(Type::getInt8PtrTy(C->getContext()));
        }
        baseInfo.insert(make_pair(C, BasePtr));

        return BasePtr;
    }

    ConstantExpr *CE = dyn_cast<ConstantExpr>(C);
    if (CE == nullptr)
        // return ConstantExpr::getPointerCast(C,
        //     Type::getInt8PtrTy(C->getContext()));
        return ConstantPointerNull::get(Type::getInt8PtrTy(C->getContext()));

    switch (CE->getOpcode())
    {
        case Instruction::GetElementPtr:
        {
            GEPOperator *GEP = cast<GEPOperator>(CE);
            assert(GEP != nullptr);
            Value *Ptr = GEP->getPointerOperand();
            Constant *CPtr = dyn_cast<Constant>(Ptr);
            assert(CPtr != nullptr);
            BasePtr = calcBasePtr(F, CPtr, I, baseInfo);
            break;
        }
        case Instruction::BitCast:
            BasePtr = calcBasePtr(F, CE->getOperand(0), I, baseInfo);
            break;
        case Instruction::Select:
        {
            Value *BasePtrA = calcBasePtr(F, CE->getOperand(1), 
                I, baseInfo);
            Value *BasePtrB = calcBasePtr(F, CE->getOperand(1), 
                I, baseInfo);
            IRBuilder<> builder(I);
            BasePtr = builder.CreateSelect(CE->getOperand(0), BasePtrA, BasePtrB);

            auto ia = calcBound.find(BasePtrA);
            if (ia == calcBound.end()) {
                errs() << "[calcBasePtr (constant)]: select can not find BoundA\n";
                errs() << "  BasePtrA: " << *BasePtrA << '\n';
                abort();
            }
            Value *BoundA = ia->second;
            auto ib = calcBound.find(BasePtrB);
            if (ia == calcBound.end()) {
                errs() << "[calcBasePtr (constant)]: select can not find BoundB\n";
                errs() << "  BasePtrB: " << *BasePtrB << '\n';
                abort();
            }
            Value *BoundB = ib->second;
            Value *Bound = builder.CreateSelect(CE->getOperand(0), BoundA, BoundB);
            calcBound.insert(make_pair(BasePtr, Bound));
            break;
        }
        case Instruction::IntToPtr:
        case Instruction::ExtractElement:
        case Instruction::ExtractValue:
            // Assumed to be non-fat pointers:
            // if (option_debug)
            //     printf(" [ConstantPointerNull]: Calculate the base pointer of a constant\n");
            BasePtr = 
                ConstantPointerNull::get(Type::getInt8PtrTy(CE->getContext()));
            break;
        default:
        {
            errs() << *C << "\n";
            C->getContext().diagnose(MinFatWarning(
                "(BUG) unknown constant expression pointer type (base)"));
            BasePtr = 
                ConstantPointerNull::get(Type::getInt8PtrTy(CE->getContext()));
            break;
        }
    }

    baseInfo.insert(make_pair(C, BasePtr));
    return BasePtr;
}

/*
 * Calculates the base pointer of an object.  The base pointer of `ptr' is:
 * - NULL if ptr==NULL or other non-fat pointer.
 * - ptr if ptr is the result of an allocation (e.g. malloc() or alloca())
 * - minfat_base(ptr) otherwise.
 * See Figure 2 from "Heap Bounds Protection with Low Fat Pointers", except:
 * - Size is no longer propagated explicitly (instead we re-calculate from the
 *   base); and
 * - We also handle stack and global objects.
 */
static Value *calcBasePtr(Function *F,
    Value *Ptr, Instruction *I, PtrInfo &baseInfo)
{
    auto i = baseInfo.find(Ptr);
    if (i != baseInfo.end()) {
        return i->second;
    }

    Value *BasePtr = ConstantPointerNull::get(
        Type::getInt8PtrTy(Ptr->getContext()));
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
        BasePtr = calcBasePtr(F, GEP->getPointerOperand(), GEP, baseInfo);
    }
    else if (AllocaInst *Alloca = dyn_cast<AllocaInst>(Ptr))
    {
        if (isInterestingAlloca(Alloca))
        {
            auto i = nextInsertPoint(F, Ptr);
            IRBuilder<> builder(i.first, i.second);
            // Result of alloca is base itself
            BasePtr = builder.CreateBitCast(Alloca, builder.getInt8PtrTy());

            Value *asInt = builder.CreatePtrToInt(BasePtr, builder.getInt64Ty());
            Value *invertTag = builder.CreateAnd(asInt, MINFAT_TAG_MASK);
            Value *Tag = builder.CreateNot(invertTag);
            Tag = builder.CreateLShr(Tag, MINFAT_TAG_OFFSET);

            Value *Size = builder.CreateShl(builder.getInt64(1), Tag);
            Value *Bound = builder.CreateAdd(asInt, Size);

            calcBound.insert(make_pair(BasePtr, Bound));
        }
    }
    else if (BitCastInst *Cast = dyn_cast<BitCastInst>(Ptr))
        BasePtr = calcBasePtr(F, Cast->getOperand(0), Cast, baseInfo);
    else if (SelectInst *Select = dyn_cast<SelectInst>(Ptr))
    {
        Value *BasePtrA = calcBasePtr(F, Select->getOperand(1),
            Select, baseInfo);
        Value *BasePtrB = calcBasePtr(F, Select->getOperand(2),
            Select, baseInfo);
        IRBuilder<> builder(Select);
        BasePtr = builder.CreateSelect(Select->getOperand(0), BasePtrA,
            BasePtrB);

        auto ia = calcBound.find(BasePtrA);
        if (ia == calcBound.end()) {
            errs() << "[calcBasePtr]: select can not find BoundA\n";
            errs() << "  BasePtrA: " << *BasePtrA << '\n';
            abort();
        }
        Value *BoundA = ia->second;
        auto ib = calcBound.find(BasePtrB);
        if (ia == calcBound.end()) {
            errs() << "[calcBasePtr]: select can not find BoundB\n";
            errs() << "  BasePtrB: " << *BasePtrB << '\n';
            abort();
        }
        Value *BoundB = ib->second;
        Value *Bound = builder.CreateSelect(Select->getOperand(0), BoundA, BoundB);
        calcBound.insert(make_pair(BasePtr, Bound));
    }
    else if (Constant *C = dyn_cast<Constant>(Ptr))
        BasePtr = calcBasePtr(F, C, I, baseInfo);
    else if (isa<IntToPtrInst>(Ptr) ||
                isa<Argument>(Ptr) ||
                isa<LoadInst>(Ptr) ||
                isa<ExtractValueInst>(Ptr) ||
                isa<ExtractElementInst>(Ptr)) {
        BasePtr = calcBasePtr(F, Ptr);
    }
    else if (isa<CallInst>(Ptr) || isa<InvokeInst>(Ptr))
    {
        if (isMemoryAllocation(Ptr))
        {
            auto i = nextInsertPoint(F, Ptr);
            IRBuilder<> builder(i.first, i.second);
            // Result of memory allocation is base itself
            BasePtr = builder.CreateBitCast(Ptr, builder.getInt8PtrTy());

            Value *asInt = builder.CreatePtrToInt(BasePtr, builder.getInt64Ty());
            Value *invertTag = builder.CreateAnd(asInt, MINFAT_TAG_MASK);
            Value *Tag = builder.CreateNot(invertTag);
            Tag = builder.CreateLShr(Tag, MINFAT_TAG_OFFSET);

            Value *Size = builder.CreateShl(builder.getInt64(1), Tag);
            Value *Bound = builder.CreateAdd(asInt, Size);

            calcBound.insert(make_pair(BasePtr, Bound));
        }
        else
            BasePtr = calcBasePtr(F, Ptr);
    }
    else if (PHINode *PHI = dyn_cast<PHINode>(Ptr))
    {
        size_t numValues = PHI->getNumIncomingValues();
        IRBuilder<> builder(PHI);
        PHINode *BasePHI = builder.CreatePHI(builder.getInt8PtrTy(),
            numValues);
        PHINode *BoundPHI = builder.CreatePHI(builder.getInt64Ty(),
            numValues);

        baseInfo.insert(make_pair(Ptr, BasePHI));
        calcBound.insert(make_pair(BasePHI, BoundPHI));
        for (size_t i = 0; i < numValues; i++) {
            BasePHI->addIncoming(UndefValue::get(builder.getInt8PtrTy()),
                PHI->getIncomingBlock(i));
            BoundPHI->addIncoming(UndefValue::get(builder.getInt64Ty()),
                PHI->getIncomingBlock(i));
        }

        bool allNonFat = true;
        for (size_t i = 0; i < numValues; i++)
        {
            Value *BaseIncoming = calcBasePtr(F, PHI->getIncomingValue(i),
                PHI, baseInfo);

            auto j = calcBound.find(BaseIncoming);
            if (j == calcBound.end()) {
                errs() << "[calcBasePtr]: PHI can not find incoming Bound\n";
                errs() << "  BaseIncoming: " << *BaseIncoming << '\n';
                errs() << "  Ptr: " << *Ptr << '\n';
                abort();
            }
            Value *BoundIncoming = j->second;

            if (!isa<ConstantPointerNull>(BaseIncoming))
                allNonFat = false;
            BasePHI->setIncomingValue(i, BaseIncoming);
            BoundPHI->setIncomingValue(i, BoundIncoming);
        }
        if (allNonFat)
        {
            // Cannot erase the PHI since it may exist in baseInfo.
            baseInfo.erase(Ptr);
            baseInfo.insert(make_pair(Ptr, BasePtr));
            return BasePtr;
        }
        return BasePHI;
    }
    else
    {
        errs() << *Ptr << "\n";
        Ptr->getContext().diagnose(MinFatWarning(
                    "(BUG) unknown pointer type (base)"));
        BasePtr =
            ConstantPointerNull::get(Type::getInt8PtrTy(Ptr->getContext()));
    }

    baseInfo.insert(make_pair(Ptr, BasePtr));
    return BasePtr;
}

// -------------------------------------------------------------------------

/*
 * Get the (assumed) bounds of input pointers.  By default this is the "empty"
 * bounds, meaning that the pointer is assumed to be within bounds, but any
 * pointer arithmetic is assumed to be possibly-OOB.
 *
 * If `option_no_check_fields` is set, then offsets [0..sizeof(*ptr)] will be
 * assumed to be within bounds, effectively meaning that fields are never
 * bounds checked.  (This emulates the behavior of some other bounds checkers
 * like BaggyBounds and PAriCheck).
 */
static Bounds getInputPtrBounds(const DataLayout *DL, Value *Ptr)
{
    // if (!option_no_check_fields)
    //     return Bounds::empty();
    Type *Ty = Ptr->getType();
    PointerType *PtrTy = dyn_cast<PointerType>(Ty);
    if (PtrTy == nullptr)
        return Bounds::empty();
    Ty = PtrTy->getElementType();
    if (!Ty->isSized())
        return Bounds::empty();
    size_t size = DL->getTypeAllocSize(Ty);
    return Bounds(0, size);
}

/*
 * Get the size of a constant object.  This is very similar to getPtrBounds()
 * defined below.
 */
static Bounds getConstantPtrBounds(
    const DataLayout *DL, Constant *C, BoundsInfo &boundsInfo)
{
    if (isa<ConstantPointerNull>(C))
        return Bounds::nonFat();
    else if (isa<UndefValue>(C))
        return Bounds::nonFat();

    auto i = boundsInfo.find(C);
    if (i != boundsInfo.end())
        return i->second;

    Bounds bounds = Bounds::nonFat();
    if (GlobalVariable *GV = dyn_cast<GlobalVariable>(C))
    {
        Type *Ty = GV->getType();
        PointerType *PtrTy = dyn_cast<PointerType>(Ty);
        assert(PtrTy != nullptr);
        Ty = PtrTy->getElementType();
        size_t size = DL->getTypeAllocSize(Ty);
        if (size != 0)
        {
            // (size==0) implies unspecified size, e.g. int x[];
            bounds = Bounds(0, size);
        }
    }
    else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(C))
    {
        switch (CE->getOpcode())
        {
            case Instruction::GetElementPtr:
            {
                GEPOperator *GEP = cast<GEPOperator>(CE);
                assert(GEP != nullptr);
                bounds = getPtrBounds(DL, GEP->getPointerOperand(),
                    boundsInfo);
                if (!bounds.isUnknown() && !bounds.isNonFat())
                {
                    APInt offset(64, 0);
                    if (GEP->accumulateConstantOffset(*DL, offset) &&
                            offset.isNonNegative())
                        bounds -= offset.getZExtValue();
                    else
                        bounds = Bounds::unknown();
                }
                break;
            }
            case Instruction::BitCast:
                bounds = getConstantPtrBounds(DL, CE->getOperand(0),
                    boundsInfo);
                break;
            case Instruction::Select:
            {
                Bounds bounds1 = getConstantPtrBounds(DL,
                    CE->getOperand(1), boundsInfo);
                Bounds bounds2 = getConstantPtrBounds(DL,
                    CE->getOperand(2), boundsInfo);
                bounds = Bounds::min(bounds1, bounds2);
                break;
            }
            case Instruction::IntToPtr:
            case Instruction::ExtractElement:
            case Instruction::ExtractValue:
                // Assumed to be non-fat pointers:
                bounds = Bounds::nonFat();
                break;
            default:
            {
                errs() << *C << "\n";
                C->getContext().diagnose(MinFatWarning(
                    "(BUG) unknown constant expression pointer type (size)"));
                break;
            }
        }
    }
    else if (isa<GlobalValue>(C))
        bounds = Bounds::nonFat();
    else
    {
        errs() << *C << "\n";
        C->getContext().diagnose(MinFatWarning(
            "(BUG) unknown constant pointer type (size)"));
    }

    boundsInfo.insert(make_pair(C, bounds));
    return bounds;
}

/*
 * Analysis that attempts to statically determine the (approx.) bounds of the
 * given object pointed to by `Ptr'.
 */
static Bounds getPtrBounds(const DataLayout *DL,
    Value *Ptr, BoundsInfo &boundsInfo)
{
    auto i = boundsInfo.find(Ptr);
    if (i != boundsInfo.end())
        return i->second;

    Bounds bounds = Bounds::nonFat();
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Ptr))
    {
        bounds = getPtrBounds(DL, GEP->getPointerOperand(), boundsInfo);
        if (!bounds.isUnknown() && !bounds.isNonFat())
        {
            APInt offset(64, 0);
            if (GEP->accumulateConstantOffset(*DL, offset) &&
                    offset.isNonNegative())
                bounds -= offset.getZExtValue();
            else
                bounds = Bounds::unknown();
        }
    }
    else if (AllocaInst *Alloca = dyn_cast<AllocaInst>(Ptr))
    {
        const Value *Size = Alloca->getArraySize();
        if (isa<ConstantInt>(Size) && Alloca->getAllocatedType()->isSized())
            bounds = Bounds(0, dyn_cast<ConstantInt>(Size)->getZExtValue() *
                DL->getTypeAllocSize(Alloca->getAllocatedType()));
        else
            bounds = getInputPtrBounds(DL, Ptr);
    }
    else if (BitCastInst *Cast = dyn_cast<BitCastInst>(Ptr))
        bounds = getPtrBounds(DL, Cast->getOperand(0), boundsInfo);
    else if (SelectInst *Select = dyn_cast<SelectInst>(Ptr))
    {
        Bounds bounds1 = getPtrBounds(DL, Select->getOperand(1),
            boundsInfo);
        Bounds bounds2 = getPtrBounds(DL, Select->getOperand(2),
            boundsInfo);
        bounds = Bounds::min(bounds1, bounds2);
    }
    else if (Constant *C = dyn_cast<Constant>(Ptr))
        bounds = getConstantPtrBounds(DL, C, boundsInfo);
    else if (isa<ConstantPointerNull>(Ptr) ||
             isa<GlobalValue>(Ptr) ||
             isa<UndefValue>(Ptr))                  // Treat as non-fat
        bounds = Bounds::nonFat();
    else if (isa<IntToPtrInst>(Ptr) ||
                isa<Argument>(Ptr) ||
                isa<LoadInst>(Ptr) ||
                isa<ExtractValueInst>(Ptr) ||
                isa<ExtractElementInst>(Ptr))
        bounds = getInputPtrBounds(DL, Ptr);        // Input pointers.
    else if (isa<CallInst>(Ptr) || isa<InvokeInst>(Ptr))
    {
        uint64_t size;
        // if (isMemoryAllocation(Ptr) && getObjectSize(Ptr, size, *DL))
        //     bounds = Bounds(0, size);
        // else
            bounds = getInputPtrBounds(DL, Ptr);    // Input pointer (default).
    }
    else if (PHINode *PHI = dyn_cast<PHINode>(Ptr))
    {
        size_t numValues = PHI->getNumIncomingValues();
        bounds = Bounds::nonFat();
        boundsInfo.insert(make_pair(Ptr, Bounds::unknown()));
        for (size_t i = 0; i < numValues; i++)
        {
            Bounds boundsIn = getPtrBounds(DL, PHI->getIncomingValue(i),
                boundsInfo);
            bounds = Bounds::min(bounds, boundsIn);
            if (bounds.isUnknown())
                break;      // No point continuing.
        }
        boundsInfo.erase(Ptr);
    }
    else
    {
        errs() << *Ptr << "\n";
        Ptr->getContext().diagnose(MinFatWarning(
                    "(BUG) unknown pointer type (size)"));
    }

    boundsInfo.insert(make_pair(Ptr, bounds));
    return bounds;
}

// -------------------------------------------------------------------------

/*
 * Test if a pointer is an "ugly GEP" or not.  Ugly GEPs can violate the
 * bounds assumptions and this leads to false OOB errors.  Note that this is
 * only a problem if the LowFat pass is inserted late in the optimization
 * pipeline.  TODO: find a better solution.
 */
static bool isUglyGEP(Value *Val)
{
    Instruction *I = dyn_cast<Instruction>(Val);
    if (I == nullptr)
        return false;
    if (I->getMetadata("uglygep") != NULL)
        return true;
    else
        return false;
}

/*
 * Accumulate (into `plan') all interesting instructions and the corresponding
 * pointer to check.  Here "interesting" means that the instruction should
 * be bounds checked.
 */
static void addToPlan(const DataLayout *DL,
    BoundsInfo &boundsInfo, Plan &plan, Instruction *I, Value *Ptr,
    unsigned kind)
{
    // if (filterPtr(kind))
    //     return;
    Bounds bounds = getPtrBounds(DL, Ptr, boundsInfo);
    size_t size = 0;
    if (kind == MINFAT_OOB_ERROR_READ || kind == MINFAT_OOB_ERROR_WRITE)
    {
        Type *Ty = Ptr->getType();
        if (auto *PtrTy = dyn_cast<PointerType>(Ty))
        {
            Ty = PtrTy->getElementType();
            size = DL->getTypeAllocSize(Ty);
        }
    }
    if (bounds.isInBounds(size) && kind != MINFAT_OOB_ERROR_ESCAPE_STORE && kind != MINFAT_OOB_ERROR_MEMCPY_ONE && kind != MINFAT_OOB_ERROR_MEMCPY_TWO) {
        kind = MINFAT_PTR_INVALID;
    }
    
    plan.push_back(make_tuple(I, Ptr, kind));
}

static void getInterestingInsts(
    const DataLayout *DL, BoundsInfo &boundsInfo, Instruction *I, Plan &plan)
{
    if (I->getMetadata("nosanitize") != nullptr)
        return;
    Value *Ptr = nullptr;
    unsigned kind = MINFAT_OOB_ERROR_UNKNOWN;
    if (StoreInst *Store = dyn_cast<StoreInst>(I))
    {
        Value *Val = Store->getValueOperand();
        if (Val->getType()->isPointerTy())
        {
            addToPlan(DL, boundsInfo, plan, I, Val,
                MINFAT_OOB_ERROR_ESCAPE_STORE);
        }
        Ptr = Store->getPointerOperand();
        kind = MINFAT_OOB_ERROR_WRITE;
    }
    else if (LoadInst *Load = dyn_cast<LoadInst>(I))
    {
        Ptr = Load->getPointerOperand();
        kind = MINFAT_OOB_ERROR_READ;
    }
    else if (PtrToIntInst *Ptr2Int = dyn_cast<PtrToIntInst>(I))
    {
        set<Value *> seen;
        if (!doesIntEscape(Ptr2Int, seen))
            return;
        Ptr = Ptr2Int->getPointerOperand();
        if (isUglyGEP(Ptr))
            return;
        kind = MINFAT_OOB_ERROR_ESCAPE_PTR2INT;
    }
    else if (CallInst *Call = dyn_cast<CallInst>(I))
    // else if (CallInst *Call = dyn_cast<CallBase>(I))
    {
        // Function *F = Call->getCalledFunction();
        Value *V = Call->getCalledValue()->stripPointerCasts();
        Function *F = dyn_cast<Function>(V);
        if (F != nullptr && F->doesNotAccessMemory())
            return;
        if (F != nullptr && F->hasName()) {
            StringRef fname = F->getName();
            if (fname.find("llvm.memset") != StringRef::npos) {
                Module *M = F->getParent();
                Value *minfat_F = M->getOrInsertFunction("minfat_memset",
                    F->getFunctionType()).getCallee();
                Call->setCalledFunction(F->getFunctionType(), minfat_F);
                return;
            }
            if (fname.find("llvm.memmove") != StringRef::npos) {
                Module *M = F->getParent();
                Value *minfat_F = M->getOrInsertFunction("minfat_memmove",
                    F->getFunctionType()).getCallee();
                Call->setCalledFunction(F->getFunctionType(), minfat_F);
                return;
            }
            if (fname.find("llvm.memcpy") != StringRef::npos) {
                Module *M = F->getParent();
                Value *minfat_F = M->getOrInsertFunction("minfat_memcpy",
                    F->getFunctionType()).getCallee();
                Call->setCalledFunction(F->getFunctionType(), minfat_F);
                return;
            }
        }
        for (unsigned i = 0; i < Call->getNumArgOperands(); i++)
        {
            Value *Arg = Call->getArgOperand(i);
            if (Arg->getType()->isPointerTy())
            {
                addToPlan(DL, boundsInfo, plan, I, Arg,
                    MINFAT_OOB_ERROR_ESCAPE_CALL);
            }
        }
        return;
    }
    else if (InvokeInst *Invoke = dyn_cast<InvokeInst>(I))
    {
        // Function *F = Invoke->getCalledFunction();
        Value *V = Invoke->getCalledValue()->stripPointerCasts();
        Function *F = dyn_cast<Function>(V);
        if (F != nullptr && F->doesNotAccessMemory())
            return;
        if (F != nullptr && F->hasName()) {
            StringRef fname = F->getName();
            if (fname.find("llvm.memset") != StringRef::npos) {
                Module *M = F->getParent();
                Value *minfat_F = M->getOrInsertFunction("minfat_memset",
                    F->getFunctionType()).getCallee();
                Invoke->setCalledFunction(F->getFunctionType(), minfat_F);
                return;
            }
            if (fname.find("llvm.memmove") != StringRef::npos) {
                Module *M = F->getParent();
                Value *minfat_F = M->getOrInsertFunction("minfat_memmove",
                    F->getFunctionType()).getCallee();
                Invoke->setCalledFunction(F->getFunctionType(), minfat_F);
                return;
            }
            if (fname.find("llvm.memcpy") != StringRef::npos) {
                Module *M = F->getParent();
                Value *minfat_F = M->getOrInsertFunction("minfat_memcpy",
                    F->getFunctionType()).getCallee();
                Invoke->setCalledFunction(F->getFunctionType(), minfat_F);
                return;
            }
        }
        for (unsigned i = 0; i < Invoke->getNumArgOperands(); i++)
        {
            Value *Arg = Invoke->getArgOperand(i);
            if (Arg->getType()->isPointerTy())
            {
                addToPlan(DL, boundsInfo, plan, I, Arg,
                    MINFAT_OOB_ERROR_ESCAPE_CALL);
            }
        }
        return;
    }
    else if (ReturnInst *Return = dyn_cast<ReturnInst>(I))
    {
        Ptr = Return->getReturnValue();
        if (Ptr == nullptr || !Ptr->getType()->isPointerTy())
            return;
        kind = MINFAT_OOB_ERROR_ESCAPE_RETURN;
    }
    else if (InsertValueInst *Insert = dyn_cast<InsertValueInst>(I))
    {
        Ptr = Insert->getInsertedValueOperand();
        if (!Ptr->getType()->isPointerTy())
            return;
        kind = MINFAT_OOB_ERROR_ESCAPE_INSERT;
    }
    else if (InsertElementInst *Insert = dyn_cast<InsertElementInst>(I))
    {
        Ptr = Insert->getOperand(1);
        if (!Ptr->getType()->isPointerTy())
            return;
        kind = MINFAT_OOB_ERROR_ESCAPE_INSERT;
    }
    else if (AtomicRMWInst *Atomic = dyn_cast<AtomicRMWInst>(I))
    {
        Ptr = Atomic->getPointerOperand();
        kind = MINFAT_OOB_ERROR_WRITE;
    }
    else if (AtomicCmpXchgInst *Atomic = dyn_cast<AtomicCmpXchgInst>(I))
    {
        Ptr = Atomic->getPointerOperand();
        kind = MINFAT_OOB_ERROR_WRITE;
    }
    else
        return;

    addToPlan(DL, boundsInfo, plan, I, Ptr, kind); 
}

// -------------------------------------------------------------------------

static bool instrumentCallExt(CallSite *CS, Value *Ptr) {
    Value *V = CS->getCalledValue()->stripPointerCasts();
    Function *F = dyn_cast<Function>(V);

    if (!F) {
        // return false;
        // errs() << "[instrumentCallExt]: Checking nameless\n nameless: true\n";
        return true;
    }

    bool debug = false;
    // StringRef fname = F->getName();
    // if (fname.contains("print"))
    // {
    //     // return true;
    //     debug = true;
    //     errs() << "[instrumentCallExt]: " << fname << '\n';
    //     // return true;
    // }

    if (F->isVarArg()) {
        if (debug)
            errs() << " VarArg: true\n";
        return true;
    }

    if (!F->isDeclaration() && !F->isDeclarationForLinker()) {  /* not external */
        unsigned arg_pos = -1;
        for (unsigned i = 0; i < CS->getNumArgOperands(); i++) {
            Value *Arg = CS->getArgOperand(i);
            if (Arg == Ptr) {
                arg_pos = i;
                break;
            }
        }
        if (CS->paramHasAttr(arg_pos + 1, Attribute::ByVal)) {
            if (debug)
                errs() << " ByVal: true\n";
            return true;
        }
        if (debug)
            errs() << " Internal: false\n";
        return false;
    }


    if (F->isIntrinsic() /* && hasPointerArg(F) */) {
        switch (F->getIntrinsicID()) {
            case Intrinsic::dbg_declare:
            case Intrinsic::dbg_value:
            case Intrinsic::lifetime_start:
            case Intrinsic::lifetime_end:
            case Intrinsic::invariant_start:
            case Intrinsic::invariant_end:
            case Intrinsic::eh_typeid_for:
            case Intrinsic::eh_return_i32:
            case Intrinsic::eh_return_i64:
            case Intrinsic::eh_sjlj_functioncontext:
            case Intrinsic::eh_sjlj_setjmp:
            case Intrinsic::eh_sjlj_longjmp:
            case Intrinsic::memcpy:
            case Intrinsic::memmove:
            case Intrinsic::memset:
                if (debug)
                    errs() << " Intrinsic: false\n";
                return false; /* No masking */
            case Intrinsic::vastart:
            case Intrinsic::vacopy:
            case Intrinsic::vaend:
                if (debug)
                    errs() << " Intrinsic: true\n";
                break; /* Continue with masking */
            default:
                errs() << "Unhandled intrinsic that takes pointer: " << *F << "\n";
                break; /* Do mask to be sure. */
        }
    }
    if (debug)
        errs() << " other: true\n";

    return true;
}

static void maskNestedPointers(Value *V, CompositeType *EltTy, 
        SmallVector<Value*, 4> &indices, IRBuilder<> &builder) {
    unsigned n = EltTy->isStructTy() ?
        cast<StructType>(EltTy)->getNumElements() :
        cast<ArrayType>(EltTy)->getNumElements();

    for (unsigned i = 0; i < n; i++) {
        Type *Ty = EltTy->getTypeAtIndex(i);

        if (Ty->isPointerTy()) {
            // DEBUG_LINE("masking nested pointer of type " << *Ty << " in value: " << *V);
            indices.push_back(builder.getInt32(i));
            Value *Ptr = builder.CreateInBoundsGEP(V, indices, "nestedgep");
            indices.pop_back();
            Value *AsInt = builder.CreatePtrToInt(Ptr, builder.getInt64Ty());
            Value *MaskedPtr = builder.CreateAnd(AsInt, MINFAT_PTR_MASK);
            MaskedPtr = builder.CreateIntToPtr(MaskedPtr, Ptr->getType());
            
            Value *Load = builder.CreateLoad(MaskedPtr, "nestedval");
            AsInt = builder.CreatePtrToInt(Load, builder.getInt64Ty());
            Value *Masked = builder.CreateAnd(AsInt, MINFAT_PTR_MASK);
            Masked = builder.CreateIntToPtr(Masked, Load->getType());

            builder.CreateStore(Masked, MaskedPtr);
        }
        else if (Ty->isAggregateType()) {
            indices.push_back(builder.getInt32(i));
            maskNestedPointers(V, cast<CompositeType>(Ty), indices, builder);
            indices.pop_back();
        }
    }
}

static void insertBoundsCheck(const DataLayout *DL, Instruction *I, Value *Ptr,
    unsigned info, const PtrInfo &baseInfo)
{
    Module *M = I->getModule();
    IRBuilder<> builder(I);
    auto i = baseInfo.find(Ptr);
    if (i == baseInfo.end())
    {
missing_baseptr_error:
        errs() << *Ptr << "\n";
        Ptr->getContext().diagnose(MinFatWarning(
            "(BUG) missing base pointer"
        ));
        return;
    }

    Value *BasePtr = i->second;
    if (BasePtr == nullptr)
        goto missing_baseptr_error;

    if (isa<ConstantPointerNull>(BasePtr))
    {
        // This is a nonfat pointer.
        return;
    }

    size_t access_size = 0;
    if (info == MINFAT_OOB_ERROR_READ || info == MINFAT_OOB_ERROR_WRITE) {
        Type *Ty = Ptr->getType();
        if (PointerType *PtrTy = dyn_cast<PointerType>(Ty)) {
            Type *eleTy = PtrTy->getElementType();
            access_size = DL->getTypeStoreSize(eleTy);
        }
    }

    // Value *ptr_debug = M->getOrInsertFunction("minfat_ptr_debug", 
    //     builder.getVoidTy(),
    //     builder.getInt8PtrTy(),
    //     nullptr);

    auto j = calcBound.find(BasePtr);
    if (j == calcBound.end()) {
        errs() << "[insertBoundsCheck]: can not find bound\n";
        errs() << "  BasePtr: " << *BasePtr << '\n';
        abort();
    }
    Value *Bound = j->second;

    Value *replacePtr = nullptr;
    // Value *F = M->getOrInsertFunction("minfat_oob_check", 
    //     builder.getInt8PtrTy(),
    //     builder.getInt8PtrTy(), builder.getInt8PtrTy(), builder.getInt64Ty(), 
    //     nullptr);
    Value *F = M->getOrInsertFunction("minfat_oob_check_with_bound", 
        builder.getInt8PtrTy(),
        builder.getInt8PtrTy(), builder.getInt8PtrTy(), builder.getInt64Ty(), builder.getInt64Ty()).getCallee();
    Value *argPtr = builder.CreateBitCast(Ptr, builder.getInt8PtrTy());
    Value *accessSize = builder.getInt64(access_size);

    Value *retPtr = builder.CreateCall(F, {argPtr, BasePtr, Bound, accessSize});
    // Value *retPtr = builder.CreateCall(F, {argPtr, BasePtr, accessSize});

    replacePtr = builder.CreateBitCast(retPtr, Ptr->getType());

    // if (isa<StoreInst>(I) || isa<LoadInst>(I) || isa<PtrToIntInst>(I) || isa<	InsertValueInst>(I) || isa<ReturnInst>(I)) {
    if (isa<LoadInst>(I) || isa<StoreInst>(I)) {
        Value *asInt = builder.CreatePtrToInt(replacePtr, builder.getInt64Ty());
        replacePtr = builder.CreateAnd(asInt, MINFAT_PTR_MASK);
        replacePtr = builder.CreateIntToPtr(replacePtr, Ptr->getType());
    }
    // else if (isa<StoreInst>(I)) {
    //     StoreInst *Store = dyn_cast<StoreInst>(I);
    //     if (Store->getPointerOperand() == Ptr) {
    //         Value *asInt = builder.CreatePtrToInt(replacePtr, builder.getInt64Ty());
    //         replacePtr = builder.CreateAnd(asInt, MINFAT_PTR_MASK);
    //         replacePtr = builder.CreateIntToPtr(replacePtr, Ptr->getType());
    //     }
    // }
    else if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
        CallSite CS(I);
        bool need_mask = false;

        Value *V = CS.getCalledValue()->stripPointerCasts();
        Function *F = dyn_cast<Function>(V);

        // if (F != nullptr) {
        //     StringRef tmpname = F->getName();
        //     if (tmpname.contains("_ZN13NEDFileBuffer3getE10my_yyltype")) {
        //         errs() << "[insertBoundsCheck]: Found NEDFileBuffer::get(my_yyltype)\n";
        //     }
        // }

        need_mask = instrumentCallExt(&CS, Ptr);
        // need_mask = true;

        if (need_mask) {
            // bool instrument_debug = false;
            // if (F != nullptr) {
            //     StringRef tmpname = F->getName();
            //     if (tmpname.contains("_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE7reserveEm")) {
            //         errs() << "[insertBoundsCheck]: function reserve\n";
            //         errs() << *I << '\n';
            //         instrument_debug = true;
            //     }
            // }

            static std::map<StringRef, std::vector<unsigned>> whitelist = {
                /* inlined std::list::push_back */
                // {"_ZNSt8__detail15_List_node_base7_M_hookEPS0_", {1}},
                /* inlined std::string += std::string */
                // {"_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE9_M_appendEPKcm", {0}},
                // {"_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE10_M_replaceEmmPKcm", {2}},
                // {"_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE9_M_mutateEmmPKcm", {2}},
                // {"_ZNKSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE7compareEPKc", {0}},
                // {"_ZNSt7__cxx1119basic_istringstreamIcSt11char_traitsIcESaIcEEC1ERKNS_12basic_stringIcS2_S3_EESt13_Ios_Openmode", {0}},
                // {"_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE9_M_assignERKS4_", {0}},
                // {"_ZNKSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE4findEPKcmm", {0}},
                // {"_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE7reserveEm", {0}}
            };
            if (F != nullptr) {
                // StringRef fname = F->getName();
                // auto it = whitelist.find(fname);
                // bool instrument_nested = false;
                // if (it != whitelist.end()) {
                //     instrument_nested = true;
                // }
                // else {
                //     Type *EltTy = cast<PointerType>(replacePtr->getType())->getElementType();
                //     if (EltTy->isStructTy()) {
                //         StringRef name = EltTy->getStructName();
                //         errs() << "[insertBoundsCheck]: param name: " << name << '\n';
                //         if (name.contains("class.std::__cxx11::basic_string")) {
                //             instrument_nested = true;
                //         }
                //     }
                // }

                // if (instrument_nested) {
                //     assert(F->isDeclaration());
                //     Type *EltTy = cast<PointerType>(replacePtr->getType())->getElementType();
                //     if (EltTy->isAggregateType()) {
                //         SmallVector<Value*, 4> indices = {builder.getInt64(0)};
                //         maskNestedPointers(replacePtr, cast<CompositeType>(EltTy), indices, builder);
                //     }
                // }
            }
            Value *asInt = builder.CreatePtrToInt(replacePtr, builder.getInt64Ty());
            replacePtr = builder.CreateAnd(asInt, MINFAT_PTR_MASK);
            replacePtr = builder.CreateIntToPtr(replacePtr, Ptr->getType());
        }
    }

    if (User *IAsUser = dyn_cast<User>(I))
        IAsUser->replaceUsesOfWith(Ptr, replacePtr);
    else {
        printf(" [insertBoundsCheck]: Instruction cannot cast to User!\n");
        errs() << *I << "\n";
        abort();
    }

}

// -------------------------------------------------------------------------

/*
 * Replace unsafe library functions.
 */
#include <malloc.h>
#define STRING(a)   STRING2(a)
#define STRING2(a)  #a
#define REPLACE2(M, N, alloc)                                           \
    do {                                                                \
        if (Function *F0 = (M)->getFunction(N)) {                       \
            Value *F1 = (M)->getOrInsertFunction("minfat_" N,           \
                F0->getFunctionType()).getCallee();                     \
            F0->replaceAllUsesWith(F1);                                 \
            Function *F2 = dyn_cast<Function>(F1);                      \
            if ((alloc) && F2 != nullptr) {                             \
                F2->setDoesNotThrow();                                  \
                F2->addAttribute(0, Attribute::NonNull);                \
            }                                                           \
        }                                                               \
    } while (false);
#define REPLACE(M, F, alloc)      REPLACE2(M, STRING(F), alloc)
static void replaceUnsafeLibFuncs(Module *M)
{
    REPLACE(M, memset, false);
    REPLACE(M, memcpy, false);
    REPLACE(M, memmove, false);

    REPLACE(M, malloc, true);
    REPLACE(M, free, false);
    REPLACE(M, calloc, true);
    REPLACE(M, realloc, true);

    // REPLACE(M, posix_memalign, false);
    // REPLACE(M, aligned_alloc, true);
    // REPLACE(M, valloc, true);
    // REPLACE(M, memalign, true);
    // REPLACE(M, pvalloc, true);

    REPLACE(M, strdup, true);
    REPLACE(M, strndup, true);

    REPLACE2(M, "_Znwm", true);                 // C++ new
    REPLACE2(M, "_Znam", true);                 // C++ new[]
    REPLACE2(M, "_ZdlPv", false);               // C++ delete
    REPLACE2(M, "_ZdaPv", false);               // C++ delete[]
    REPLACE2(M, "_ZnwmRKSt9nothrow_t", true);   // C++ new nothrow
    REPLACE2(M, "_ZnamRKSt9nothrow_t", true);   // C++ new[] nothrow
}

static void addMinFatFunctions(Module *M)
{
    Function *F = nullptr;

    // minfat_base(void *ptr) returns a tagged base pointer of ptr
    // 1. get tag from the top bits of ptr
    // 2. get base pointer by masking off the offset from ptr
    // 3. tag the base pointer
    // In the base pointer returned, tag is the inverted value
    // *** argument 'ptr' is a tagged pointer ***
    // F = M->getFunction("minfat_base");
    // if (F != nullptr)
    // {
    //     BasicBlock *Entry = BasicBlock::Create(M->getContext(), "", F);

    //     IRBuilder<> builder(Entry);

    //     Value *Ptr = &F->getArgumentList().front();
    //     Value *AsInt = builder.CreatePtrToInt(Ptr, builder.getInt64Ty());
        
    //     Value *invertTag = builder.CreateAnd(AsInt, MINFAT_TAG_MASK, "inverted tag");
        
    //     Value *Tag = builder.CreateNot(invertTag);
    //     Tag = builder.CreateLShr(Tag, MINFAT_TAG_OFFSET);
    //     // Value *size = builder.CreateShl(builder.getInt64(1),size_base);

    //     Value *Mask = builder.CreateShl(builder.getInt64(0xFFFFFFFFFFFFFFFF), Tag);
    //     // Value *TPtr = builder.CreateBitCast(Ptr, builder.getInt64Ty());
    //     Value *TPtr = builder.CreateAnd(AsInt, Mask);
    //     TPtr = builder.CreateOr(TPtr, invertTag);
    //     TPtr = builder.CreateIntToPtr(TPtr, builder.getInt8PtrTy());
    //     builder.CreateRet(TPtr);

    //     F->setOnlyReadsMemory();
    //     F->setDoesNotThrow();
    //     F->setLinkage(GlobalValue::InternalLinkage);
    //     F->addFnAttr(llvm::Attribute::AlwaysInline);
    // }

    // void* minfat_oob_check_rt(void *ptr, void *base, size_t access_size)
    F = M->getFunction("minfat_oob_check");
    if (F != nullptr)
    {
        BasicBlock *Entry = BasicBlock::Create(M->getContext(), "", F);

        IRBuilder<> builder(Entry);
        // auto i = F->arg_begin();
        Value *Ptr = F->getArg(0);
        Value *Base = F->getArg(1);
        Value *AccessSize = F->getArg(2);

        Value *BaseAsInt = builder.CreatePtrToInt(Base, builder.getInt64Ty());
        Value *Tag = builder.CreateAnd(BaseAsInt, MINFAT_TAG_MASK);
        Value *SizeBase = builder.CreateNot(Tag);
        SizeBase = builder.CreateLShr(SizeBase, MINFAT_TAG_OFFSET);
        SizeBase = builder.CreateAnd(SizeBase, 0x3F);
        Value *Size = builder.CreateShl(builder.getInt64(1), SizeBase);

        Value *PtrAsInt = builder.CreatePtrToInt(Ptr, builder.getInt64Ty());
        Value *MaskedPtr = builder.CreateAnd(PtrAsInt, MINFAT_PTR_MASK);
        Value *TaggedPtr = builder.CreateOr(MaskedPtr, Tag);
        // Value *TaggedPtr = PtrAsInt;

        Value *Bound = builder.CreateAdd(BaseAsInt, Size);
        Value *AccessBound = builder.CreateSub(Bound, AccessSize);

        Value *RPtr = TaggedPtr;

        // Value *Cmp1 = builder.CreateICmpULT(TaggedPtr, BaseAsInt);
        // RPtr = builder.CreateSelect(Cmp1, BaseAsInt, RPtr);

        Value *Cmp2 = builder.CreateICmpUGT(TaggedPtr, AccessBound);
        RPtr = builder.CreateSelect(Cmp2, AccessBound, RPtr);

        RPtr = builder.CreateIntToPtr(RPtr, builder.getInt8PtrTy());

        builder.CreateRet(RPtr);

        // F->setOnlyReadsMemory();
        F->setDoesNotThrow();
        F->setLinkage(GlobalValue::InternalLinkage);
        F->addFnAttr(llvm::Attribute::AlwaysInline);
    }

    F = M->getFunction("minfat_oob_check_with_bound");

    if (F != nullptr)
    {
        auto it = F->arg_begin ();
        Value *Ptr = &*it++;
        // i++;
        Value *Base = &*it++;
        // i++;
        Value *Bound = &*it++;
        // i++;
        Value *AccessSize = &*it++;
        // i++;



        BasicBlock *Entry = BasicBlock::Create(M->getContext(), "", F);

        IRBuilder<> builder(Entry);
        // auto i = F->arg_begin();


        Value *BaseAsInt = builder.CreatePtrToInt(Base, builder.getInt64Ty());
        Value *Tag = builder.CreateAnd(BaseAsInt, MINFAT_TAG_MASK);

        Value *PtrAsInt = builder.CreatePtrToInt(Ptr, builder.getInt64Ty());
        Value *MaskedPtr = builder.CreateAnd(PtrAsInt, MINFAT_PTR_MASK);
        Value *TaggedPtr = builder.CreateOr(MaskedPtr, Tag);
        // Value *TaggedPtr = PtrAsInt;

        Value *AccessBound = builder.CreateSub(Bound, AccessSize);

        Value *RPtr = TaggedPtr;

        Value *Cmp1 = builder.CreateICmpULT(TaggedPtr, BaseAsInt);
        RPtr = builder.CreateSelect(Cmp1, BaseAsInt, RPtr);

        Value *Cmp2 = builder.CreateICmpUGT(TaggedPtr, AccessBound);
        RPtr = builder.CreateSelect(Cmp2, AccessBound, RPtr);

        RPtr = builder.CreateIntToPtr(RPtr, builder.getInt8PtrTy());

        builder.CreateRet(RPtr);

        // F->setOnlyReadsMemory();
        F->setDoesNotThrow();
        F->setLinkage(GlobalValue::InternalLinkage);
        F->addFnAttr(llvm::Attribute::AlwaysInline);
    }
}

// -------------------------------------------------------------------------

/*
 * Convert an alloca instruction into a low-fat-pointer.  This is a more
 * complicated transformation described in the paper:
 * "Stack Bounds Protection with Low Fat Pointers", in NDSS 2017.
 */
 /*
 * minifat pointer does not need the stack mirror to the heap
 * but needs align and size as 2^n
 */
static void tagAllocaPtr(Module *M, Instruction *I)
{
    AllocaInst *Alloca = dyn_cast<AllocaInst>(I);
    if (Alloca == nullptr)
        return;

    const DataLayout *DL = &M->getDataLayout();
    Value *Size = Alloca->getArraySize();
    Type *Ty = Alloca->getAllocatedType();
    ConstantInt *ISize = dyn_cast<ConstantInt>(Size);
    Function *F = I->getParent()->getParent();
    auto i = nextInsertPoint(F, Alloca);
    IRBuilder<> builder(i.first, i.second);
    Value *AllocedPtr = nullptr;
    
    Value *NoReplace = nullptr;
    bool delAlloca = false;

    if (ISize != nullptr) {
        // Fix length stack object

        size_t ori_size = DL->getTypeAllocSize(Ty) * ISize->getZExtValue();
        size_t new_size = 1ull << (64 - clz(ori_size));
        // STEP (1): Align the stack:
        size_t align = new_size;
        if (align > Alloca->getAlignment())
            Alloca->setAlignment(MaybeAlign(align));
        
        // STEP (2): Adjust the allocation size:
        if (new_size != ori_size)
        {
            /*
             * LLVM doubles the allocSz when the object is allocSz-aligned for
             * some reason (gcc does not seem to do this).  This wastes space
             * but it does not seem there is anything we can do about it.
             */
            Size = builder.getInt64(new_size);
            AllocaInst *NewAlloca = builder.CreateAlloca(
                builder.getInt8Ty(), Size);
            NewAlloca->setAlignment(MaybeAlign(Alloca->getAlignment()));
            AllocedPtr = NewAlloca;
            delAlloca = true;
        }
        else {
            Size = builder.getInt64(ori_size);
            AllocedPtr = builder.CreateBitCast(Alloca, builder.getInt8PtrTy());
        }
    }
    else {
        // Variable length stack object
        errs() << "Variable length stack object\n";
        return;
        // abort();

        delAlloca = true;

        // STEP (1): Get the actual allocation size
        Size = builder.CreateMul(builder.getInt64(DL->getTypeAllocSize(Ty)), Size);
        Value *C = M->getOrInsertFunction("minfat_stack_allocsize",
            builder.getInt64Ty(),
            builder.getInt64Ty(),
            nullptr).getCallee();
        Size = builder.CreateCall(C, {Size});
        if (CallInst *Call = dyn_cast<CallInst>(Size))
            Call->setTailCall(true);

        // STEP (2): Create replacement alloca()
        Value *CastAlloca = builder.CreateAlloca(builder.getInt8Ty(), Size);
        Value *SP = CastAlloca;     // SP = Stack Pointer

        // STEP (3): Align the stack
        C = M->getOrInsertFunction("minfat_sp_align",
            builder.getInt8PtrTy(),
            builder.getInt8PtrTy(), builder.getInt64Ty(),
            nullptr).getCallee();
        Value * alignedSP = builder.CreateCall(C, {SP, Size});
        SP = builder.CreateBitCast(alignedSP, SP->getType());
        NoReplace = SP;

        // STEP (4): Save the adjusted stack pointer
        C = M->getOrInsertFunction("llvm.stackrestore",
            builder.getVoidTy(),
            builder.getInt8PtrTy(),
            nullptr).getCallee();
        Value *_ = builder.CreateCall(C, {SP});
        if (CallInst *Call = dyn_cast<CallInst>(_))
            Call->setTailCall(true);

        AllocedPtr = SP;
    }
    NoReplace = AllocedPtr;

    // if (option_debug) {
    //     printf(" [tagAllocaPtr]: alloca info\n");
    //     printf("  ori_size: %lu\n  new_size: %lu\n  ori_align: %lu\n  new_align: %lu\n", ori_size, new_size, ori_align, dyn_cast<AllocaInst>(AllocedPtr)->getAlignment());
    // }

    assert(AllocedPtr->Type() == builder.getInt8PtrTy());
    // Tag the pointer returned by Alloca
    // AllocedPtr is the alignment adjusted pointer
    // Size is the actual allocation size
    Value *Ptr;
    Value *Package = M->getOrInsertFunction("minfat_pointer_package",
        builder.getInt8PtrTy(),
        builder.getInt8PtrTy(), builder.getInt64Ty()).getCallee();
    Ptr = builder.CreateCall(Package, {AllocedPtr, Size});
    Ptr = builder.CreateBitCast(Ptr, Alloca->getType());
    // Ptr = builder.CreateBitCast(AllocedPtr, Alloca->getType());

    // Replace all uses of `Alloca' with the (now low-fat) `Ptr'.
    // We do not replace lifetime intrinsics nor values used in the
    // construction of the low-fat pointer (NoReplace1, ...).
    std::vector<User *> replace, lifetimes;
    for (User *Usr: Alloca->users())
    {
        if (Usr == NoReplace)
            continue;
        if (IntrinsicInst *Intr = dyn_cast<IntrinsicInst>(Usr))
        {
            if (Intr->getIntrinsicID() == Intrinsic::lifetime_start ||
                    Intr->getIntrinsicID() == Intrinsic::lifetime_end)
            {
                lifetimes.push_back(Usr);
                continue;
            }
        }
        if (BitCastInst *Cast = dyn_cast<BitCastInst>(Usr))
        {
            for (User *Usr2: Cast->users())
            {
                IntrinsicInst *Intr = dyn_cast<IntrinsicInst>(Usr2);
                if (Intr == nullptr)
                    continue;
                if (Intr->getIntrinsicID() == Intrinsic::lifetime_start ||
                        Intr->getIntrinsicID() == Intrinsic::lifetime_end)
                    lifetimes.push_back(Usr2);
            }
        }
        replace.push_back(Usr);
    }

    for (User *Usr : replace)
        Usr->replaceUsesOfWith(Alloca, Ptr);
    
    for (User *Usr: lifetimes)
    {
        // Lifetimes are deleted.  The alternative is to insert the mirroring
        // after the lifetime start, however, this proved too difficult to get
        // working.  One problem is intermediate casts which may be reused.
        if (auto *Lifetime = dyn_cast<Instruction>(Usr))
            Lifetime->eraseFromParent();
    }

    if (delAlloca) {
        Alloca->eraseFromParent();
    }
}

// -------------------------------------------------------------------------

#define NOINSTRUMENT_PREFIX "__noinstrument_"

static bool isNoInstrument(Value *V) {
    if (V && V->hasName()) {
        StringRef Name = V->getName();
        if (Name.startswith(NOINSTRUMENT_PREFIX))
            return true;
        // Support for mangled C++ names (should maybe do something smarter here)
        if (Name.startswith("_Z"))
            return Name.find(NOINSTRUMENT_PREFIX, 2) != StringRef::npos;
    }
    return false;
}

/*
 * Collect global variables that can be tagged (anything except environ and
 * llvm.*).
 * from deltapointer
 */
static void findGlobalsToTag(Module &M, std::vector<GlobalVariable*> &Globals) {
    for (GlobalVariable &GV : M.globals()) {
        assert(!GV.getName().startswith("tagged.") && "can only tag globals once");

        if (isNoInstrument(&GV))
            continue;

        /* Don't mask globals from libraries XXX right? */
        if (!GV.hasInitializer())
            continue;

        /* Ignore constants */
        if (GV.isConstant())
            continue;

        /* Ignore @environ bevause of getenv problems FIXME */
        if (GV.getName() == "environ")
           continue;
        // Should be caught by !hasInitializer() above:
        assert(GV.getName() != "environ");

        /* Ignore intrinsics like constructor lists */
        if (GV.getName().startswith("llvm."))
            continue;

        Globals.push_back(&GV);
    }
}

Function* createNoInstrumentFunction(Module &M, FunctionType *FnTy,
        StringRef Name, bool AlwaysInline) {
    std::string FullName(NOINSTRUMENT_PREFIX);
    FullName += Name;
    Function *F = Function::Create(FnTy, GlobalValue::InternalLinkage, FullName, &M);
    if (AlwaysInline)
        F->addFnAttr(Attribute::AlwaysInline);
    return F;
}

/*
 * Create constructor function that replaces all globals with pointers, and
 * initializes their metapointers. Insert it in the constructor list after
 * initialize_global_metadata if it exists, or at the start of the list
 * otherwise. If no constructor list exists, create it.
 */
static Function *createGlobalTagConstructor(Module &M) {
    LLVMContext &Ctx = M.getContext();
    FunctionType *FnTy = FunctionType::get(Type::getVoidTy(Ctx), false);
    Function *F = createNoInstrumentFunction(M, FnTy, "initialize_tagged_globals", false);

    /* Add function to constructor list after @initialize_global_metadata */
    GlobalVariable *OldGlobalCtors = M.getGlobalVariable("llvm.global_ctors");
    std::vector<Constant*> Ctors;
    int index = 0;

    if (OldGlobalCtors) {
        assert(OldGlobalCtors->hasNUses(0));
        OldGlobalCtors->setName("llvm.global_ctors_old");

        ConstantArray *CA = cast<ConstantArray>(OldGlobalCtors->getInitializer());
        int i = 0;

        for (Use &I : CA->operands()) {
            Ctors.push_back(cast<Constant>(I.get()));

            if (ConstantStruct *Struct = dyn_cast<ConstantStruct>(I.get())) {
                Function *Fn = cast<Function>(Struct->getAggregateElement(1));
                if (Fn->getName() == "initialize_global_metadata")
                    index = i + 1;
            }
            i++;
        }
    }

    // if (option_debug) {
    //     if (index == 0)
    //         printf(" [createGlobalTagConstructor]: Inserting global initializer at start of constructor list\n");
    //     else
    //         printf(" [createGlobalTagConstructor]: Inserting global initializer after initialize_global_metadata\n");
    // }
    

    IntegerType *i32 = Type::getInt32Ty(Ctx);
    PointerType *i8Ptr = Type::getInt8Ty(Ctx)->getPointerTo();
    StructType *StructTy = StructType::get(i32, F->getType(), i8Ptr);
    Constant *StructMembers[] = {
        ConstantInt::getSigned(i32, -1), F, ConstantPointerNull::get(i8Ptr)
    };
    Constant *NewEntry = ConstantStruct::get(StructTy, StructMembers);
    Ctors.insert(Ctors.begin() + index, NewEntry);

    ArrayType *CtorsTy = ArrayType::get(StructTy, Ctors.size());
    new GlobalVariable(M, CtorsTy, false, GlobalValue::AppendingLinkage,
            ConstantArray::get(CtorsTy, Ctors), "llvm.global_ctors");

    if (OldGlobalCtors)
        OldGlobalCtors->eraseFromParent();

    return F;
}

static void tagGlobalVariables(Module &M) {
    vector<GlobalVariable*> Globals;
    findGlobalsToTag(M, Globals);

    if (Globals.empty()) {
        // if (option_debug)
        //     printf(" [tagGlobalVariables]: no global\n");
        return;
    }
    else {
        // if (option_debug) {
        //     for (auto G : Globals) {
        //         cout << " [tagGlobalVariables]: " << G->getName().str() << endl;
        //     }
        // }
    }

    const DataLayout DL = M.getDataLayout ();

    Function *F = createGlobalTagConstructor(M);
    IRBuilder<> builder(BasicBlock::Create(F->getContext(), "entry", F));

    size_t align = 0;
    for (GlobalVariable *GV : Globals) {
        PointerType *ptrTy = GV->getType();
        Type *elementType = ptrTy->getElementType();
        size_t ori_size = DL.getTypeAllocSize(elementType);

        size_t tag = 64 - clz(ori_size);
        size_t new_size = 1ull << tag;
        if (new_size > align)
            align = new_size;
    }
    // if (option_debug)
    //     cout << "[tagGlobalVariables]: new alignment is " << align << endl;

    for (GlobalVariable *GV : Globals) {
        PointerType *ptrTy = GV->getType();
        GlobalVariable *taggedGV = new GlobalVariable(M, builder.getInt8PtrTy(), false,
                GlobalValue::InternalLinkage, ConstantPointerNull::get(builder.getInt8PtrTy()),
                Twine("tagged.") + GV->getName());

        // Maybe there are problems about ori_size, need double check
        Type *elementType = ptrTy->getElementType();
        size_t ori_size = DL.getTypeAllocSize(elementType);

        size_t tag = 64 - clz(ori_size);
        // size_t new_size = 1ull << tag;
        tag = (~tag) & 0x3F;

        // if (option_debug) {
        //     cout << " [tagGlobalVariables]: @" << GV->getName().str();
        //     cout << " ori_size is " << ori_size;
        //     cout << " new_size is " << new_size;
        //     cout << endl;
        // }

        GV->setAlignment(align);
        Value *asInt = builder.CreatePtrToInt(GV, builder.getInt64Ty());
        Value *invertTag = builder.getInt64(tag);
        Value *highBits = builder.CreateShl(invertTag, MINFAT_TAG_OFFSET);
        Value *taggedPtrInt = builder.CreateOr(asInt, highBits);
        // Value *taggedPtr = builder.CreateBitCast(GV, builder.getInt8PtrTy());
        Value *taggedPtr = builder.CreateIntToPtr(taggedPtrInt, builder.getInt8PtrTy());
        builder.CreateStore(taggedPtr, taggedGV);

        globalInfo.insert(make_pair(GV, taggedGV));
    }
    builder.CreateRetVoid();
    
    return;
}

// ------------------------------------------------------------------------

namespace
{

struct SMA : public ModulePass
{
    static char ID;
    SMA() : ModulePass(ID) { }

    virtual bool runOnModule(Module &M)
    {
        // if (option_debug)
        // {
        //     printf(" [main pipeline]: SMA begin\n");
        // }

        // PASS (1): Bounds instrumentation
        const DataLayout *DL = &M.getDataLayout();

        // PASS (1b) Make global variable minfat
        tagGlobalVariables(M);

        // for (auto &F : M) {
        //     StringRef fname = F.getName();
        //     errs() << "Function: " << fname << '\n';
        //     if (F.isDeclaration())
        //         errs() << " isDeclaration\n";
        //     if (F.isDeclarationForLinker())
        //         errs() << " isDeclarationForLinker\n";
        // }

        for (auto &F : M)
        {
            if (F.isDeclaration())
                continue;
            if (isNoInstrument(&F))
                continue;

            Plan plan;
            BoundsInfo boundsInfo;
            PtrInfo baseInfo;

            vector<Value*> cmpInsts;

            calcBound.clear();
            Value *NullPtr = ConstantPointerNull::get(Type::getInt8PtrTy(M.getContext()));
            Value *NullBound = ConstantInt::get(Type::getInt64Ty(M.getContext()), 0x8000000000000000);
            calcBound.insert(make_pair(NullPtr, NullBound));
            
            // STEP 1: Find all instructions that we need to instrument
            
            for (auto &BB : F)
                for (auto &I : BB) {
                    getInterestingInsts(DL, boundsInfo, &I, plan);
                    if (isa<CmpInst>(&I))
                        cmpInsts.push_back(&I);
                }

            // STEP 2: Calculate the base pointers
            set<Instruction*> interestingInsts;
            for (auto &p : plan) {
                calcBasePtr(&F, get<1>(p), get<0>(p), baseInfo);
                interestingInsts.insert(get<0>(p));
            }

            // STEP 3: Add the bounds check
            for (auto &p : plan)
                insertBoundsCheck(DL, get<0>(p), get<1>(p), get<2>(p),
                    baseInfo);

            // for (auto I : interestingInsts)
            //     maskInterstingInsts(I);

            for (auto I : cmpInsts) {
                CmpInst *cmp = dyn_cast<CmpInst>(I);
                unsigned op_num = cmp->getNumOperands();
                // bool ptr_op = false;
                // bool not_ptr_op = false;
                // bool instrument = false;
                // for (unsigned i = 0; i < op_num; i++) {
                //     Value *Op = cmp->getOperand(i);
                //     if (Op->getType()->isPointerTy()) {
                //         ptr_op = true;
                //     }
                //     else {
                //         not_ptr_op = true;
                //     }
                // }
                // instrument = ptr_op && ~not_ptr_op;
                for (unsigned i = 0; i < op_num; i++) {
                    Value *Op = cmp->getOperand(i);
                    if (Op->getType()->isPointerTy()) {
                        IRBuilder<> builder(cmp);
                        Value *AsInt = builder.CreatePtrToInt(Op, builder.getInt64Ty());
                        AsInt = builder.CreateAnd(AsInt, MINFAT_PTR_MASK);
                        Value *Masked = builder.CreateIntToPtr(AsInt, Op->getType());
                        cmp->replaceUsesOfWith(Op, Masked);
                    }
                }
            }
        }

        // PASS (1a) Make stack pointer minfat
        for (auto &F : M)
        {
            if (F.isDeclaration())
                continue;
            if (isNoInstrument(&F))
                continue;
            
            vector<Instruction *> allocas;
            for (auto &BB : F)
                for (auto &I : BB)
                    if (isInterestingAlloca(&I)) {
                        allocas.push_back(&I);
                        // taggedAlloca.insert(&I);
                    }
            for (auto *I : allocas)
                tagAllocaPtr(&M, I);
        }

        // PASS (2): Replace unsafe library calls
        replaceUnsafeLibFuncs(&M);

        addMinFatFunctions(&M);

        if (option_debug)
        {
            string errs;
            raw_string_ostream rso(errs);
            if (verifyModule(M, &rso))
            {
                fprintf(stderr, "MinFat generated broken IR!\n");
                fprintf(stderr, "%s\n", errs.c_str());
                abort();
            }
        }

        return true;
    }

    /*
     * Analysis usage specification.
     */
    virtual void getAnalysisUsage(AnalysisUsage &AU) const
    {
        AU.addRequired<TargetLibraryInfoWrapperPass>();
    }
};

}

char SMA::ID = 0;
namespace llvm
{
    ModulePass *createSMAPass()
    {
        return new SMA();
    }
}