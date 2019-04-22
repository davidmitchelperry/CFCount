// CFCount.cpp
// Implements a model of a specific execution path of a C program 
// as a Z3Py script. Adds additional statments to the script
// that bit-blasts the model and converts it from SMT to
// Z3's internal representation for SAT

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/CommandLine.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/StringRef.h"

#include <vector>
#include <queue>
#include <map>
#include <set>
#include <queue>
#include <stack>
#include <string>
#include <fstream>
#include <algorithm>
#include <iterator>
#include <iostream>
#include <fstream>
#include <sstream>

#include "llvm/Analysis/CFG.h"

using namespace llvm;

#define DEBUG_TYPE "hello"

/** Required Parameters for LLVM Pass **/

// Trace file indicating what path in the program is being modeled
cl::opt<std::string> TraceFilename(cl::Positional, cl::Required,
                                   cl::desc("<trace file>"));
// Name of the resulting Z3Py file that converts path conditions to Z3's SAT
// format
cl::opt<std::string> Z3Filename(cl::Positional, cl::Required,
                                cl::desc("<z3 file>"));
// File indicating the upper and lower bounds of input variables in the program
// being modeled
cl::opt<std::string> BoundsFilename(cl::Positional, cl::Required,
                                    cl::desc("<bounds file>"));
// File to track the name of boolean variables created in the model
// (needed later when converting Z3's output to standard SAT format, CNF
cl::opt<std::string> BoolFilename(cl::Positional, cl::Required,
                                  cl::desc("<bool file>"));

/***************************************/

std::ofstream result_file;

Module *mod_ptr;

std::vector<int> lowerBounds;
std::vector<int> upperBounds;
int boundCt = 0;

// Struct for tracking state information
// of functions executed on the path being
// modeled
typedef struct states {
  std::string returnVar;
  std::map<std::string, int> locals;
} State;

std::stack<State *> stateStack;

// Struct for tracking information
// about what a poniter points to
typedef struct pointsTo {
  std::string name;
  // if it points to an array
  bool isArray;
  // If it points to an offset in an array that is based
  // on an input variable
  bool arrayOffsetSymb;
  // Name of input variable that indiciates the offset
  std::string symOffsetName;
  // If the offset is known, what is it
  int concreteOffset;
  // Type information about the array being pointed to
  int arrayBitWidth;
} PointsTo;

std::map<std::string, PointsTo *> pointsToMap;
std::map<std::string, int> arrayMap;

// Struct for tracking info about Nodes in the path's
// Control Flow Graph
struct CFGNode {
  // Name of the BB
  std::string name;
  // Pointer to the LLVM BB structure
  BasicBlock *BB;
  // List of instructions in the BB
  std::vector<Instruction *> instructions;
  // All of the children nodes
  std::vector<CFGNode *> children;
  // All of the parent nodes
  std::vector<CFGNode *> parents;
  // If the node has been visited yet
  bool visited;
};

void getCFGChildren(Instruction *control_flow_inst, CFGNode *result,
                    std::map<std::string, CFGNode *> *BBMap) {

  // If the Control Flow Instruction is a branch
  if (BranchInst *bi = dyn_cast<BranchInst>(control_flow_inst)) {
    int succNum = bi->getNumSuccessors();
    // If only 1 successor
    if (succNum == 1) {
      // Get the label name of successor
      std::string succName = bi->getOperand(0)->getName().str();
      struct CFGNode *CFGChildNode;
      // If successor is already in the table
      if (BBMap->find(succName) != BBMap->end()) {
        CFGChildNode = &*(BBMap->find(succName)->second);
      } else {
        CFGChildNode = new CFGNode;
        CFGChildNode->visited = false;
        BBMap->insert(
            std::pair<std::string, CFGNode *>(succName, CFGChildNode));
      }
      CFGChildNode->parents.push_back(result);
      // Add child node to current BB's children list
      result->children.push_back(CFGChildNode);

    } else {
      // For each target of the branch instruction
      for (int i = 1; i <= succNum; ++i) {
        // Get the label name of successor
        std::string succName = bi->getOperand(i)->getName().str();
        struct CFGNode *CFGChildNode;
        // If successor is already in the table
        if (BBMap->find(succName) != BBMap->end()) {
          CFGChildNode = &*(BBMap->find(succName)->second);
        } else {
          CFGChildNode = new CFGNode;
          CFGChildNode->visited = false;
          BBMap->insert(
              std::pair<std::string, CFGNode *>(succName, CFGChildNode));
        }
        CFGChildNode->parents.push_back(result);
        // Add child node to current BB's children list
        result->children.push_back(CFGChildNode);
      }
    }
  }

  // If the Control Flow Instruction is a switch branch
  if (SwitchInst *si = dyn_cast<SwitchInst>(control_flow_inst)) {
    for (unsigned int i = 0; i < si->getNumSuccessors(); ++i) {

      BasicBlock *succ = si->getSuccessor(i);
      std::string succName = succ->getName().str();

      struct CFGNode *CFGChildNode;
      // If successor is already in the table
      if (BBMap->find(succName) != BBMap->end()) {
        CFGChildNode = &*(BBMap->find(succName)->second);
      } else {
        CFGChildNode = new CFGNode;
        CFGChildNode->visited = false;
        BBMap->insert(
            std::pair<std::string, CFGNode *>(succName, CFGChildNode));
      }
      CFGChildNode->parents.push_back(result);
      // Add child node to current BB's children list
      result->children.push_back(CFGChildNode);
    }
  }
}

struct CFGNode *InsertCFGNode(BasicBlock *bb,
                              std::map<std::string, CFGNode *> *BBMap) {

  struct CFGNode *result;
  // If BBNode has already been created
  if (BBMap->find(bb->getName().str()) != BBMap->end()) {
    result = BBMap->find(bb->getName().str())->second;
  } else {
    result = new CFGNode;
    result->visited = false;
    BBMap->insert(
        std::pair<std::string, CFGNode *>(bb->getName().str(), result));
  }

  // Set the Name of the CFGNode
  result->name = bb->getName().str();

  // Set the BB of the CFGNode
  result->BB = bb;

  // Branch or Switch Instruction of BB
  Instruction *control_flow_inst;

  // Add all instructions of BB to the CFGNode's instruction vector
  for (BasicBlock::iterator inst = bb->begin(), inst_e = bb->end();
       inst != inst_e; ++inst) {
    control_flow_inst = &*inst;
    result->instructions.push_back(&*inst);
  }

  // Insert children info for CFG
  getCFGChildren(control_flow_inst, result, BBMap);

  return result;
}

// Rename all function parameters to a consistant format that
// guarantees there are no collisions (this is not guaranteed
// by LLVM)
void rename_func_params() {
  for (auto func = mod_ptr->begin(), func_e = mod_ptr->end(); func != func_e;
       ++func) {
    // If function is user created
    if (func->isDeclaration() == false) {
      // Ignore main's inputs
      if (func->getName().str() != "main") {
        int arg_ct = 0;
        // Change each var to the name format:
        // function name + _arg_ + parameter #
        for (auto param = func->arg_begin(); param != func->arg_end();
             ++param) {
          param->setName(func->getName().str() + "_arg_" +
                         std::to_string(arg_ct));
          arg_ct++;
        }
      }
    }
  }
}

// Rename BBs to a consistant/predicatable name
// (makes debugging much easier)
void rename_bbs() {
  for (auto func = mod_ptr->begin(), func_e = mod_ptr->end(); func != func_e;
       ++func) {
    if (func->isDeclaration() == false) {
      bool first = true;
      for (Function::iterator bb = func->begin(), bb_e = func->end();
           bb != bb_e; ++bb) {
        // Setting each basic blocks name
        if (first) {
          first = false;
          bb->setName(func->getName() + "_" + "entry");
        } else {
          bb->setName(func->getName() + "_" + "bb");
        }
      }
    }
  }
}

// Rename instructions to a consistant/predicatable name
// (makes debugging much easier)
void rename_insts() {

  for (auto func = mod_ptr->begin(), func_e = mod_ptr->end(); func != func_e;
       ++func) {
    int var_ct = 0;
    if (func->isDeclaration() == false) {
      for (Function::iterator bb = func->begin(), bb_e = func->end();
           bb != bb_e; ++bb) {
        for (BasicBlock::iterator inst = bb->begin(), inst_e = bb->end();
             inst != inst_e; ++inst) {
          if (!inst->getType()->isVoidTy()) {
            inst->setName(func->getName() + "_" + "var_" +
                          std::to_string(var_ct));
            var_ct++;
          }
        }
      }
    }
  }
}

// Read in bound information for input variables
void get_bounds() {

  std::ifstream bounds_file(BoundsFilename);
  std::string holder;

  int ct = 0;
  int curr;

  if (bounds_file.is_open()) {
    while (bounds_file >> holder) {
      std::stringstream ss(holder);
      ss >> curr;
      if (ct % 2 == 0) {
        lowerBounds.push_back(curr);
      } else {
        upperBounds.push_back(curr);
      }
      ct++;
    }
    bounds_file.close();
  } else {
    llvm::errs() << "Cannot open bounds file!\n";
  }
}

// Read in the order of basic blocks executed
// in the path being modeled
std::vector<std::string> get_trace() {

  std::ifstream trace_file(TraceFilename);
  std::vector<std::string> result;
  std::string holder;

  if (trace_file.is_open()) {
    while (trace_file >> holder) {
      if (holder != "call" && holder != "return") {
        result.push_back(holder);
      }
    }
    trace_file.close();
  } else {
    llvm::errs() << "Cannot open trace file!\n";
  }

  return result;
}

// Build a nested map for looking up BB's corresponding CFGNode
// For ex. to find the CFG for bb1 in func1 use: FunctionCFGMap[func1][bb1]
void BuildFunctionCFGMap(
    std::map<std::string, std::map<std::string, CFGNode *> > *FunctionCFGMap) {
  // BUILD BBMap
  for (auto func = mod_ptr->begin(), func_e = mod_ptr->end(); func != func_e;
       ++func) {
    if (FunctionCFGMap->find(func->getName()) != FunctionCFGMap->end()) {
      llvm::errs()
          << "BuildFunctionCFGMap Error: Function already in FunctionCFGMap\n";
    } else {
      std::map<std::string, CFGNode *> *currBBMap =
          new std::map<std::string, CFGNode *>;
      for (Function::iterator bb = func->begin(), bb_e = func->end();
           bb != bb_e; ++bb) {
        InsertCFGNode(&(*bb), currBBMap);
      }

      (*FunctionCFGMap)[func->getName().str()] = (*currBBMap);
    }
  }
}

// TODO
std::string model_library_name = "models.py";
std::string model_library_prefix = "ar";

// Indicate if you want logging information
// printed.
bool logging = true;

// Prints logging information
void print_error(std::string msg) {
  if (logging) {
    llvm::errs() << msg;
  }
}

// Get the name of the Z3 variable that models
// a specifica LLVM variable
std::string GetVarName(std::string name) {

  std::string result = "";
  // Get the symbol table for the function currently being
  // analyzed
  std::map<std::string, int> *vst = &(stateStack.top()->locals);

  if (vst->find(name) != vst->end()) {
    result = name + "_" + std::to_string((*vst)[name]);
  } else {
    print_error("GetVarName Error: Cannot find variable (" + name +
                ") in vst\n");
  }

  return result;
}

// "Create" aka assign a name for a Z3 variable
// that will model a LLVM variable
std::string CreateVarName(std::string name) {

  std::string result;
  // Get the symbol table for the function currently being
  // analyzed
  std::map<std::string, int> *vst = &(stateStack.top()->locals);

  if (vst->find(name) != vst->end()) {
    (*vst)[name] += 1;
  } else {
    (*vst)[name] = 0;
  }
  result = name + "_" + std::to_string((*vst)[name]);

  return result;
}

void GetBranchInstConstraint(BranchInst *bi, std::string nextBB,
                             std::string *result) {
  print_error("GetInstConstraint: BranchInst\n");
  std::string opName;
  // Non-conditional branches don't need to be modeled
  if (bi->getNumSuccessors() == 1) {
    print_error("GetInstConstraint: Non-conditional branch\n");
  } else if (bi->getNumSuccessors() == 2) {
    // Get the var name for the branch
    opName = GetVarName(bi->getOperand(0)->getName().str());
    // add constraints of the branch ot Z3 formula
    (*result) += "g.add(" + opName + " == ";
    // Indicate if the if or else branch was executed in
    // the trace
    if (bi->getOperand(2)->getName().str() == nextBB) {
      (*result) += "True";
    } else if (bi->getOperand(1)->getName().str() == nextBB) {
      (*result) += "False";
    } else {
      print_error("GetInstConstraint Error: Branch inst does not target the "
                  "next BB in the trace\n");
    }
    // Close the specific constraint
    (*result) += ")\n";
  }
}

void GetAllocaInstConstraint(AllocaInst *ai, std::string *result) {
  print_error("GetInstConstraint: AllocaInst\n");
  auto ai_type = ai->getAllocatedType();
  // If allocating an integer
  if (IntegerType *int_type = dyn_cast<IntegerType>(ai_type)) {
    // Get the current name of the variable
    std::string aiName = CreateVarName(ai->getName().str());
    // Get the bit width of int being allocated
    int bitWidth = int_type->getBitWidth();
    // Create the variable in Z3
    (*result) += aiName + " = BitVec('" + aiName + "', " +
                 std::to_string(bitWidth) + ")\n";
  }
  // If allocating an array
  else if (ArrayType *arr_type = dyn_cast<ArrayType>(ai_type)) {
    std::string arrayName = ai->getName().str();
    if (arrayMap.find(arrayName) != arrayMap.end()) {
      print_error("GetInstConstraint Error: Allocating array with name "
                  "already in arrayMap!\n");
    } else {
      // Get Type of array element. Currently only handles Ints
      Type *alloc_type = arr_type->getArrayElementType();
      if (IntegerType *int_type = dyn_cast<IntegerType>(alloc_type)) {
        arrayMap[arrayName] = arr_type->getArrayNumElements();
        // Create Z3 var for array
        std::string varName = CreateVarName(arrayName);
        int bitWidth = int_type->getBitWidth();
        // Use Z3 array functions to model the array
        (*result) = "temp = " + model_library_prefix + ".calloc('" + varName +
                    "', " + std::to_string(arr_type->getArrayNumElements()) +
                    ", " + std::to_string(bitWidth) + ")\n";
        // First item in result from calloc are the constraints on the
        // arrays values in Z3
        (*result) += "g.add(temp[0])\n";
        // Second item is the name of the created array
        (*result) += varName + " = temp[1]\n";
      } else {
        print_error(
            "GetInstConstraint Error: Allocating array with unknown type!\n");
      }
    }
  } else {
    print_error("GetInstConstraint: Allocation of unknown type!\n");
  }
}

// Generates constraints for geps. Only works when the gep is used
// to access an offset in an array
void GetGEPInstConstraint(GetElementPtrInst *gep, std::string *result) {

  print_error("GetInstConstraint: GetElementPtrInst\n");

  // If the operand of the gep is an allocate
  if (AllocaInst *ai = dyn_cast<AllocaInst>(gep->getOperand(0))) {
    // Ensure the operand of the gep is an array
    auto ai_type = ai->getAllocatedType();
    if (ArrayType *arr_type = dyn_cast<ArrayType>(ai_type)) {
      // Ensure the array is of a type we can handle
      std::string arrayName = ai->getName().str();
      if (arrayMap.find(arrayName) == arrayMap.end()) {
        print_error("GetInstConstraint Error: GEP on array not in arrayMap!\n");
      } else {
        // Ensure the array type is an integer
        Type *alloc_type = arr_type->getArrayElementType();
        if (IntegerType *int_type = dyn_cast<IntegerType>(alloc_type)) {
          // Track the information about what this GEP points
          // to (which array and location in array)
          PointsTo *temp = new PointsTo;
          temp->name = ai->getName();
          temp->isArray = true;
          temp->arrayBitWidth = int_type->getBitWidth();

          // If the offset is a known constant, it's concrete
          if (ConstantInt *ci = dyn_cast<ConstantInt>(gep->getOperand(2))) {
            temp->arrayOffsetSymb = false;
            temp->concreteOffset = ci->getSExtValue();
            // If it's based on an unknown value (input), it's symbolic
          } else {
            temp->arrayOffsetSymb = true;
            temp->symOffsetName = gep->getOperand(2)->getName().str();
          }
          // Create the Z3 var for the gep (array pointer)
          std::string varName = CreateVarName(gep->getName().str());
          pointsToMap[varName] = temp;
        } else {
          print_error(
              "GetInstConstraint Error: GEP on array of non-int type!\n");
        }
      }
    }
  } else {
    print_error("GetInstConstraint Error: GEP's 0th op is not an allocate!\n");
    gep->dump();
  }
}

void GetStoreInstConstraint(StoreInst *si, std::string *result) {

  print_error("GetInstConstraint: StoreInst\n");

  // If storing to an allocated variable
  if (AllocaInst *store_ai = dyn_cast<AllocaInst>(si->getOperand(1))) {
    // Ensure it's an integer
    if (IntegerType *int_type =
            dyn_cast<IntegerType>(si->getOperand(0)->getType())) {
      // Get some more type info
      int bitWidth = int_type->getBitWidth();
      // Get the name of the Z3 variable corresponding to the value being stored
      std::string valToStore = GetVarName(si->getOperand(0)->getName().str());
      // Create a Z3 variable for the variable being stored to (Important to
      // note that a new variable is created anytime a store occurs. This
      // is necessary for a SMT language and is essentially SSA form)
      std::string storingTo = CreateVarName(si->getOperand(1)->getName().str());
      // Generate the Z3 constraints that model the store
      (*result) = storingTo + " = BitVec('" + storingTo + "', " +
                  std::to_string(bitWidth) + ")\n";
      (*result) += "g.add(" + storingTo + " == " + valToStore + ")\n";
    } else {
      print_error("GetInstConstraint: storing to unhandled type\n");
      si->getType()->dump();
    }
  } else {
    // Storing to a pointer
    print_error("GetInstConstraint: store to a pointer!\n");
    // Get the name of the pointer
    std::string ptrName = GetVarName(si->getOperand(1)->getName().str());
    // Make sure it is a pointer we can handle
    if (pointsToMap.find(ptrName) != pointsToMap.end()) {
      pointsTo *temp = pointsToMap[ptrName];
      // Stores to arrays are currently not supported
      if (temp->isArray) {
        print_error("storing to an array!\n");
      } else {
        // If storing to an integer pointer
        if (IntegerType *int_type =
                dyn_cast<IntegerType>(si->getOperand(0)->getType())) {
          int bitWidth = int_type->getBitWidth();
          // Create a Z3 variable for storing to
          std::string storingTo = CreateVarName(temp->name);
          // Get the Z3 for the value being stored
          std::string valToStore =
              GetVarName(si->getOperand(0)->getName().str());
          // Generate constraints to enforce store
          (*result) = storingTo + " = BitVec('" + storingTo + "', " +
                      std::to_string(bitWidth) + ")\n";
          (*result) += "g.add(" + storingTo + " == " + valToStore + ")\n";
        } else {
          print_error("storing to a pointer that points to non int type!\n");
        }
      }
    } else {
      print_error(
          "Could not find the pointer being stored to in pointsToMap!\n");
    }
  }
}

void GetLoadInstConstraint(LoadInst *li, std::string *result) {

  print_error("GetInstConstraint: LoadInst\n");
  // If loading an integer
  if (li->getType()->isIntegerTy()) {

    // Get some more type info about the int
    int instBitWidth;
    if (IntegerType *val_ty = dyn_cast<IntegerType>(li->getType())) {
      instBitWidth = val_ty->getBitWidth();
    } else {
      print_error("GetInstConstraint Error: LoadInst returned to a non "
                  "integer type value!\n");
    }

    // Create the Z3 variable for the loadA
    std::string varName = CreateVarName(li->getName().str());
    // Get the value being loaded
    Value *load_op = li->getOperand(0);

    // If loading an allocate (typical case)
    if (AllocaInst *op_ai = dyn_cast<AllocaInst>(load_op)) {
      auto ai_type = op_ai->getAllocatedType();
      // If allocated type is an integer
      if (IntegerType *int_type = dyn_cast<IntegerType>(ai_type)) {
        // Get the Z3 variable for value that is being loaded
        std::string loadOpName = GetVarName(op_ai->getName().str());
        (*result) = varName + " = BitVec('" + varName + "', " +
                    std::to_string(instBitWidth) + ")\n";
        // Generate the Z3 constraint for the load
        (*result) += "g.add(" + varName + " == " + loadOpName + ")\n";
      } else {
        print_error("GetInstConstraint Error: LoadInst operand 0 is an "
                    "allocate of unknown type.\n");
      }
    } else {
      print_error("Loading an instruction that is not an allocate!\n");
      // Loading non-allocate. Typically means that a pointer is being
      // dereferenced

      // Get the Z3 variable for what is being loaded
      std::string loadOpName = GetVarName(load_op->getName().str());
      // Make sure the value is a pointer we can handle
      if (pointsToMap.find(loadOpName) != pointsToMap.end()) {
        pointsTo *temp = pointsToMap[loadOpName];
        std::string pointsToName = GetVarName(temp->name);
        // Can't handle loads of pointers to arrays (arrays alloc'd
        // dynamically)
        if (temp->isArray) {
          print_error("loading pointer to array!\n");
        } else {
          // Generate Z3 constraints for pointer load
          (*result) = varName + " = BitVec('" + varName + "', " +
                      std::to_string(instBitWidth) + ")\n";
          (*result) += "g.add(" + varName + " == " + pointsToName + ")\n";
        }
      } else {
        print_error("Loading something that is not an allocate or pointer in "
                    "pointsToMap!\n");
      }
    }
  } else {
    print_error("GetInstConstraint Error: LoadInst unhandled type\n");
    li->dump();
  }
}

void GetBinaryOperatorConstraint(BinaryOperator *bo, std::string *result) {

  print_error("GetInstConstraint: BinaryOperator\n");

  // Get type info about Bin op result
  int instBitWidth;
  if (IntegerType *val_ty = dyn_cast<IntegerType>(bo->getType())) {
    instBitWidth = val_ty->getBitWidth();

  } else {
    print_error("GetInstConstraint Error: BinaryOperator returned to a non "
                "integer type value!\n");
  }

  // Create a Z3 var for the bin op's result
  std::string varName = CreateVarName(bo->getName().str());

  // Declare the variable in Z3 formula
  (*result) = varName + " = BitVec('" + varName + "', " +
              std::to_string(instBitWidth) + ")\n";

  // Get Z3 variable for the left and right hand side of the bin
  // op. Can be a constant or another variable
  std::string lhs, rhs;
  if (ConstantInt *ci = dyn_cast<ConstantInt>(bo->getOperand(0))) {
    lhs = std::to_string(ci->getSExtValue());
  } else {
    lhs = GetVarName(bo->getOperand(0)->getName().str());
  }
  if (ConstantInt *ci = dyn_cast<ConstantInt>(bo->getOperand(1))) {
    rhs = std::to_string(ci->getSExtValue());
  } else {
    rhs = GetVarName(bo->getOperand(1)->getName().str());
  }

  // The prefix of the Z3 constraint that encodes the
  // bin op
  (*result) += "g.add(" + varName + " == (" + lhs;

  // Handle each specific type of bin op
  if (bo->getOpcode() == Instruction::Add) {
    (*result) += " + ";
  } else if (bo->getOpcode() == Instruction::Sub) {
    (*result) += " - ";
  } else if (bo->getOpcode() == Instruction::Mul) {
    (*result) += " * ";
  } else if (bo->getOpcode() == Instruction::UDiv) {
    (*result) += " / ";
  } else if (bo->getOpcode() == Instruction::SDiv) {
    (*result) += " / ";
  } else if (bo->getOpcode() == Instruction::URem) {
    (*result) += " % ";
  } else if (bo->getOpcode() == Instruction::SRem) {
    (*result) += " % ";
  }

  // Sufix of the Z3 constraint
  (*result) += rhs + "))\n";
}

void GetCmpInstConstraint(CmpInst *ci, std::string *result) {

  print_error("GetInstConstraint: CmpInst\n");

  // Create a Z3 variable to hold result of cmp inst
  std::string varName = CreateVarName(ci->getName().str());

  // Get Z3 Variables for left and right hand side of
  // cmp inst (can be concrete or symbolic)
  std::string left_hand_side, right_hand_side;
  if (ConstantInt *c = dyn_cast<ConstantInt>(ci->getOperand(0))) {
    left_hand_side = std::to_string(c->getSExtValue());
  } else {
    left_hand_side = GetVarName(ci->getOperand(0)->getName().str());
    if (left_hand_side == "") {
      print_error("GetInstConstraint Error: left hand side of cmpinst not "
                  "foud in vst\n");
    }
  }
  if (ConstantInt *c = dyn_cast<ConstantInt>(ci->getOperand(1))) {
    right_hand_side = std::to_string(c->getSExtValue());
  } else {
    right_hand_side = GetVarName(ci->getOperand(1)->getName().str());
    if (right_hand_side == "") {
      print_error("GetInstConstraint Error: right hand side of cmpinst not "
                  "foud in vst\n");
    }
  }

  // Mark the new variable as a bool and add to the
  // bool output file (used later for conversion to
  // standard CNF format)
  (*result) = varName + " = Bool('" + varName + "')\n";
  std::ofstream bool_file(BoolFilename, std::ofstream::app);
  bool_file << varName << "\n";
  bool_file.close();

  // Generate the proper Z3 constraint based on the type
  // of cmp inst
  if (ci->getPredicate() == CmpInst::ICMP_EQ) {
    print_error("ICMP_EQ\n");
    (*result) += "g.add(" + varName + " == (" + left_hand_side + " == " +
                 right_hand_side + "))";
  } else if (ci->getPredicate() == CmpInst::ICMP_NE) {
    print_error("ICMP_NE\n");
    (*result) += "g.add(" + varName + " == (" + left_hand_side + " != " +
                 right_hand_side + "))";
  } else if (ci->getPredicate() == CmpInst::ICMP_SGT) {
    print_error("ICMP_NE\n");
    (*result) += "g.add(" + varName + " == (" + left_hand_side + " > " +
                 right_hand_side + "))";
  } else if (ci->getPredicate() == CmpInst::ICMP_SGE) {
    print_error("ICMP_SGE\n");
    (*result) += "g.add(" + varName + " == (" + left_hand_side + " >= " +
                 right_hand_side + "))";
  } else if (ci->getPredicate() == CmpInst::ICMP_SLT) {
    print_error("ICMP_SLT\n");
    (*result) += "g.add(" + varName + " == (" + left_hand_side + " < " +
                 right_hand_side + "))";
  } else if (ci->getPredicate() == CmpInst::ICMP_SLE) {
    print_error("ICMP_SLE\n");
    (*result) += "g.add(" + varName + " == (" + left_hand_side + " <= " +
                 right_hand_side + "))";
  }
  (*result) += "\n";
}

void GetPHINodeConstraint(PHINode *pn, std::string prevBB,
                          std::string *result) {

  print_error("GetInstConstraint: PHINode\n");
  std::string incomingValName;

  // Get the incoming value for the PHINode. Essentially, find the specific
  // BB that was executed in the trace and propogate its value forward to
  // the phinode instruction
  std::string incomingVal = "";
  for (int i = 0; i < pn->getNumIncomingValues(); i++) {
    if (pn->getIncomingBlock(i)->getName().str() == prevBB) {
      if (ConstantInt *ci = dyn_cast<ConstantInt>(pn->getIncomingValue(i))) {
        incomingVal = std::to_string(ci->getSExtValue());
      } else {
        incomingVal = GetVarName(pn->getIncomingValue(i)->getName());
        incomingValName = pn->getIncomingValue(i)->getName().str();
        if (incomingVal == "") {
          print_error("GetInstConstraint Error: Cannot find phinode return "
                      "val in val symb table\n");
        }
      }
    }
  }

  if (incomingVal == "") {
    print_error(
        "GetInstConstraint Error: Can't find incoming value for PHINode\n");
    print_error("prevBB: " + prevBB + "\n");
  }

  int instBitWidth;
  // If the phi is an int
  if (IntegerType *val_ty = dyn_cast<IntegerType>(pn->getType())) {
    // Get some more type info and generate the Z3 constraints
    // for the phi (similar to a store)
    instBitWidth = val_ty->getBitWidth();
    std::string varName = CreateVarName(pn->getName().str());
    (*result) = varName + " = BitVec('" + varName + "', " +
                std::to_string(instBitWidth) + ")\n";
    (*result) += "g.add(" + varName + " == " + incomingVal + ")\n";
  }
  // If the phi is apointer
  else if (PointerType *ptr_ty = dyn_cast<PointerType>(pn->getType())) {
    llvm::errs() << "PHINode for pointer type!\n";
    // If the pointer has been seen in previous exeuctions
    // aka the pointer points to something
    if (pointsToMap.find(incomingVal) != pointsToMap.end()) {
      print_error("PHINode result is a pointer to a pointer!\n");
      // Do some book keeping for the pointer info, and create
      // pointer variable
      PointsTo *temp = new PointsTo;
      temp->name = pointsToMap[incomingVal]->name;
      temp->isArray = pointsToMap[incomingVal]->isArray;
      temp->arrayOffsetSymb = pointsToMap[incomingVal]->arrayOffsetSymb;
      temp->symOffsetName = pointsToMap[incomingVal]->symOffsetName;
      temp->concreteOffset = pointsToMap[incomingVal]->concreteOffset;
      temp->arrayBitWidth = pointsToMap[incomingVal]->arrayBitWidth;
      std::string varName = CreateVarName(pn->getName().str());
      pointsToMap[varName] = temp;
    } else {
      // If the pointer has only been allocated but doesn't
      // point to anything. Create the struct for the pointer
      // and create a Z3 variable for it
      PointsTo *temp = new PointsTo;
      temp->name = incomingValName;
      temp->isArray = false;
      temp->arrayOffsetSymb = false;

      // NOTE: Creating a variable name here for the pointer doesn't really
      // make sense.
      // We don't ever create a variable for the pointer itself so this is
      // likely
      // unnecessary
      std::string varName = CreateVarName(pn->getName().str());
      pointsToMap[varName] = temp;
    }
  } else {
    print_error("GetInstConstraint Error: PHINode returned to a non integer "
                "type value!\n");
  }
}

void GetSExtInstConstraint(SExtInst *si, std::string *result) {

  print_error("GetInstConstraint: SExtInst\n");
  int extend_by;
  int instBitWidth;

  // If Sign extending an int
  if (IntegerType *val_ty = dyn_cast<IntegerType>(si->getType())) {
    if (IntegerType *op_ty =
            dyn_cast<IntegerType>(si->getOperand(0)->getType())) {
      // Compute how much we are extending by (used in the
      // Z3 constraint) and the final bit width
      extend_by = val_ty->getBitWidth() - op_ty->getBitWidth();
      instBitWidth = val_ty->getBitWidth();
    } else {
      print_error(
          "GetInstConstraint Error: SExtInst on a non integer type value!\n");
    }
  } else {
    print_error("GetInstConstraint Error: SExtInst returned to a non integer "
                "type value!\n");
  }

  // Create a new Z3 variable for the result of the sign extend
  std::string varName = CreateVarName(si->getName().str());
  (*result) = varName + " = BitVec('" + varName + "', " +
              std::to_string(instBitWidth) + ")\n";

  // Get the Z3 variable for the value being extended
  std::string opVar = GetVarName(si->getOperand(0)->getName().str());
  // Lookup current version of operand
  if (opVar == "") {
    print_error("GetInstConstraint Error: No active version of SExt "
                "instruction operand\n");
  }

  // Generate the Z3 constraint for sign extending
  (*result) += "g.add(" + varName + " == SignExt(" + std::to_string(extend_by) +
               ", " + opVar + "))";
}

void GetTrunInstConstraint(TruncInst *ti, std::string *result) {

  print_error("GetInstConstraint: TruncInst\n");

  // Get the width of int after performing the truncation
  int instBitWidth;
  if (IntegerType *val_ty = dyn_cast<IntegerType>(ti->getType())) {
    instBitWidth = val_ty->getBitWidth();
  } else {
    print_error("GetInstConstraint Error: TrunInst returned to a non integer "
                "type value!\n");
  }

  // Create a new Z3 var for storing the truncated variable
  std::string varName = CreateVarName(ti->getName().str());
  // Get the Z3 variable for the value being truncated
  std::string opName = GetVarName(ti->getOperand(0)->getName().str());
  // Declare the new variable
  (*result) = varName + " = BitVec('" + varName + "', " +
              std::to_string(instBitWidth) + ")\n";
  // Encode the truncation in Z3
  (*result) += "g.add(" + varName + " == Extract(" +
               std::to_string(instBitWidth - 1) + ", 0, " + opName + "))\n";
}

void GetReturnInstConstraint(ReturnInst *ri, std::string *result) {

  print_error("GetInstConstraint: ReturnInst\n");

  // Get the name of the function that is returning
  Function *ret_func = ri->getParent()->getParent();
  // If main, nothing has to be modeled
  if (ret_func->getName().str() == "main") {
  }
  // If null is being returned the function is void
  else if (ri->getReturnValue() == NULL) {
    print_error("returning void!\n");
  }
  // If returning from non-main and non-void function
  else {
    print_error(
        "GetInstConstraint: ReturnInst found in function not named main\n");
    // Only handle functions that return ints
    Type *ret_type = ri->getOperand(0)->getType();
    if (IntegerType *int_type = dyn_cast<IntegerType>(ret_type)) {
      print_error("returning int type!\n");
      // Get type info of returne dvalue
      int retBitWidth = int_type->getBitWidth();
      // Declare the Z3 variable designated for storing
      // the function's returned value
      (*result) = stateStack.top()->returnVar + " = BitVec('" +
                  stateStack.top()->returnVar + "', " +
                  std::to_string(retBitWidth) + ")\n";
      // If returning a constant int
      if (ConstantInt *cons_int = dyn_cast<ConstantInt>(ri->getOperand(0))) {
        (*result) += "g.add(" + stateStack.top()->returnVar + " == " +
                     std::to_string(cons_int->getSExtValue()) + ")\n";
      }
      // If returning a variable
      else {
        std::string returnOpName =
            GetVarName(ri->getOperand(0)->getName().str());
        (*result) += "g.add(" + stateStack.top()->returnVar + " == " +
                     returnOpName + ")\n";
      }
      // Remove the current function from the trace stack
      stateStack.pop();
    }
  }
}

void GetAtoiInstConstraint(CallInst *ci, std::string *result) {
  // Create Z3 variable for atoi result
  std::string varName = CreateVarName(ci->getName().str());
  // Get Z3 variable for atoi argument
  std::string opName =
      GetVarName(ci->getOperand(0)->getName().str() + "_array");
  // Declare the resulting Z3 variable and encode it
  (*result) = varName + " = BitVec('" + varName + "', 32)\n";
  (*result) += "g.add(" + model_library_prefix + ".atoi(" + opName + ", " +
               varName + "))\n";
}

void GetCallocInstConstraint(CallInst *ci, std::string *result) {
  // Create Z3 variables for the array being allocated,
  // the offset for which the array pointer points to,
  // and the length of the array
  std::string varName_array = CreateVarName(ci->getName().str() + "_array");
  std::string varName_offset = CreateVarName(ci->getName().str() + "_offset");
  std::string varName_array_length =
      CreateVarName(ci->getName().str() + "_array_length");

  // Number elements to allocate
  std::string opName0;
  // Size of elements being allocated
  std::string opName1;

  // The number of elements is either a constant or some variable
  // in the program
  if (ConstantInt *con = dyn_cast<ConstantInt>(ci->getOperand(0))) {
    opName0 = std::to_string(con->getSExtValue());
  } else {
    opName0 = GetVarName(ci->getOperand(0)->getName().str());
  }

  // Get the size of elements being allocated (only handles concrete
  // sizes)
  if (ConstantInt *con = dyn_cast<ConstantInt>(ci->getOperand(1))) {
    opName1 = std::to_string(con->getSExtValue() * 8);
  } else {
    print_error("GetInstConstraint Error: size argument to calloc is not "
                "constant\n");
  }

  // Generate Z3 constraints for calloc (using the generated
  // model call)
  (*result) = "temp = " + model_library_prefix + ".calloc('" + varName_array +
              "', " + opName0 + ", " + opName1 + ")\n";
  (*result) += "g.add(temp[0])\n";
  (*result) += varName_array + " = temp[1]\n";
  (*result) += varName_offset + " = BitVec('" + varName_offset + "', 64)\n";
  (*result) += "g.add(" + varName_offset + " == 0)\n";
  (*result) +=
      varName_array_length + " = BitVec('" + varName_array_length + "', 64)\n";
  (*result) += "g.add(" + varName_array_length + " == " + opName0 + ")\n";
}

void GetMemsetInstConstraint(CallInst *ci, std::string *result) {
  // Create variables for the resulting array,
  // the offset of the pointer to the resulting array,
  // and the length of the resulting array
  std::string varName_array = CreateVarName(ci->getName().str() + "_array");
  std::string varName_offset = CreateVarName(ci->getName().str() + "_offset");
  std::string varName_array_length =
      CreateVarName(ci->getName().str() + "_array_length");

  // Get variable names for the original array and its length
  std::string opName0 =
      GetVarName(ci->getOperand(0)->getName().str() + "_array");
  std::string opName0_length =
      GetVarName(ci->getOperand(0)->getName().str() + "_array_length");
  std::string opName1, opName2;

  // Get the Z3 var for the value being set
  // (can be a constant or a program variable)
  if (ConstantInt *cons_int = dyn_cast<ConstantInt>(ci->getOperand(1))) {
    opName1 = std::to_string(cons_int->getSExtValue());
  } else {
    opName1 = GetVarName(ci->getOperand(1)->getName().str());
  }

  // Get the  Z3 var for the number of bytes to set
  // (can be a constant or a program variable)
  if (ConstantInt *cons_int = dyn_cast<ConstantInt>(ci->getOperand(2))) {
    opName2 = std::to_string(cons_int->getSExtValue());
  } else {
    opName2 = GetVarName(ci->getOperand(2)->getName().str());
  }

  // Use the Z3 modeling library to model the calloc call
  (*result) = "temp = " + model_library_prefix + ".memset(" + opName0 + ", '" +
              varName_array + "', 0, " + opName1 + ", " + opName2 + ", 8)\n";
  (*result) += "g.add(temp[0])\n";
  (*result) += varName_array + " = temp[1]\n";
  (*result) += varName_offset + " = BitVec('" + varName_offset + "', 64)\n";
  (*result) += "g.add(" + varName_offset + " == 0)\n";
  (*result) +=
      varName_array_length + " = BitVec('" + varName_array_length + "', 64)\n";
  (*result) +=
      "g.add(" + varName_array_length + " == " + opName0_length + ")\n";
}

void GetPowInstConstraint(CallInst *ci, std::string *result) {
  // Create Z3 variable for result
  std::string varName = CreateVarName(ci->getName().str());
  // Get Z3 Variables for ops
  std::string opName0 = GetVarName(ci->getOperand(0)->getName().str());
  std::string opName1 = GetVarName(ci->getOperand(1)->getName().str());
  // Declare the new Z3 variable for the result
  (*result) = varName + " = BitVec('" + varName + "', 32)\n";
  // Use the pow model created
  (*result) += "g.add(" + model_library_prefix + ".pow(" + opName0 + ", " +
               opName1 + ", " + varName + "))\n";
}

void GetStrlenInstConstraint(CallInst *ci, std::string *result) {

  int instBitWidth;

  // Get the resulting variable's bit width
  if (IntegerType *val_ty = dyn_cast<IntegerType>(ci->getType())) {
    instBitWidth = val_ty->getBitWidth();

  } else {
    print_error("GetInstConstraint Error: strlen returned to a non "
                "integer type value!\n");
  }

  // Create a Z3 variable for the strlen result
  std::string varName = CreateVarName(ci->getName().str());
  // Get the Z3 variable for the array that is strlen's argument
  std::string opName_array =
      GetVarName(ci->getOperand(0)->getName().str() + "_array");
  // Declare the Z3 variable for the result
  (*result) = varName + " = BitVec('" + varName + "', " +
              std::to_string(instBitWidth) + ")\n";
  // Use the generated model for strlen
  (*result) += "g.add(" + model_library_prefix + ".strlen(" + opName_array +
               ", " + varName + "))\n";
}

void GetScanfInstConstraint(CallInst *ci, std::string *result) {

  // For each of scanf's arguments
  for (int i = 1; i < ci->getNumArgOperands(); i++) {
    // If the argument is an allocation, it's an input variable
    if (AllocaInst *ai = dyn_cast<AllocaInst>(ci->getArgOperand(i))) {
      // Get the Z3 var for the input variable
      std::string argName = GetVarName(ci->getArgOperand(i)->getName().str());
      // Place the correct bounds on the input variable
      (*result) += "g.add(And(" + model_library_prefix + ".gte(" + argName +
                   ", " + std::to_string(lowerBounds[boundCt]) + "), " +
                   model_library_prefix + ".lte(" + argName + ", " +
                   std::to_string(upperBounds[boundCt]) + ")))\n";
    } else {
      // If the argument is a pointer
      if (PointerType *ptr_type =
              dyn_cast<PointerType>(ci->getArgOperand(i)->getType())) {
        // Get the Z3 variable for the pointer
        std::string argName = GetVarName(ci->getArgOperand(i)->getName().str());
        // If it's a pointer that we can handle (it points to
        // something
        if (pointsToMap.find(argName) != pointsToMap.end()) {

          // Get what it points to
          PointsTo *temp = pointsToMap[argName];

          // If it points to an array
          if (temp->isArray == true) {
            // Can't handle the read at symbolic location
            if (temp->arrayOffsetSymb) {
              print_error("scanf arg is symbolic array read\n");
            }
            // Place the scanf input value into the array
            // at some concrete location
            else {
              std::string readVar = CreateVarName("readVar");
              (*result) += readVar + " = BitVec('" + readVar + "', " +
                           std::to_string(temp->arrayBitWidth) + ")\n";
              (*result) += "g.add(" + model_library_prefix + ".array_read(" +
                           temp->name + ", " +
                           std::to_string(temp->concreteOffset) + ", " +
                           readVar + "))\n";
              (*result) += "g.add(And(" + model_library_prefix + ".gte(" +
                           readVar + ", " +
                           std::to_string(lowerBounds[boundCt]) + "), " +
                           model_library_prefix + ".lte(" + readVar + ", " +
                           std::to_string(upperBounds[boundCt]) + ")))\n";
            }
          }
          // If the pointer points to something that's not an array
          else {
            (*result) += "g.add(And(" + model_library_prefix + ".gte(" +
                         temp->name + ", " +
                         std::to_string(lowerBounds[boundCt]) + "), " +
                         model_library_prefix + ".lte(" + temp->name + ", " +
                         std::to_string(upperBounds[boundCt]) + ")))\n";
          }
        } else {
          print_error("GetInstConstraint Error: Scanf Arg is a pointer "
                      "not in pointsToMap\n");
        }
      }
    }
    boundCt++;
  }
}

void GetUserFuncInstConstraint(CallInst *ci, std::string *result) {

  // Get all the Z3 variables for each argument passed to the
  // function (variables are local to the function making the call)
  int arg_ct = 0;
  std::vector<std::string> passedArgs;
  for (auto arg = ci->getCalledFunction()->arg_begin();
       arg != ci->getCalledFunction()->arg_end(); ++arg) {
    Type *arg_type = arg->getType();
    if (IntegerType *int_ty = dyn_cast<IntegerType>(arg_type)) {
      std::string opName =
          GetVarName(ci->getArgOperand(arg_ct)->getName().str());
      passedArgs.push_back(opName);
    } else if (PointerType *ptr_ty = dyn_cast<PointerType>(arg_type)) {
      std::string opName =
          GetVarName(ci->getArgOperand(arg_ct)->getName().str());
      passedArgs.push_back(opName);
    } else {
      print_error(
          "GetInstConstraint Error: unhandled function argument type\n");
      ci->getArgOperand(arg_ct)->dump();
    }
    arg_ct++;
  }

  // Get the type of the value being returned by the function
  Type *retType = ci->getCalledFunction()->getReturnType();
  int instBitWidth;
  if (IntegerType *int_ty = dyn_cast<IntegerType>(retType)) {
    instBitWidth = int_ty->getBitWidth();
    // Get the name of func's return var, initialize the called func's new
    // state, and push it on the stateStack
    std::string varName = CreateVarName(ci->getName().str());
    State *calledFuncState = new State;
    calledFuncState->returnVar = varName;
    stateStack.push(calledFuncState);
  } else if (retType->isVoidTy()) {
  } else {
    print_error("GetInstConstraint Error: unhandled function return type\n");
    ci->getArgOperand(arg_ct)->dump();
  }

  // Handle the called function arguments
  // Essentially, create a new variable Z3 for the function
  // parameters and set them to being equal to the
  // values that were passed
  arg_ct = 0;
  for (auto arg = ci->getCalledFunction()->arg_begin();
       arg != ci->getCalledFunction()->arg_end(); ++arg) {
    Type *arg_type = arg->getType();
    // If an integer is passed
    if (IntegerType *int_ty = dyn_cast<IntegerType>(arg_type)) {
      int instBitWidth;
      instBitWidth = int_ty->getBitWidth();
      // Create a new Z3 variable, declare it, and assign
      // it to its passed value
      std::string varName = CreateVarName(arg->getName().str());
      (*result) += varName + " = " + "BitVec('" + varName + "', " +
                   std::to_string(instBitWidth) + ")\n";
      (*result) += "g.add(" + varName + " == " + passedArgs[arg_ct] + ")\n";
    }
    // If a pointer is passed
    else if (PointerType *ptr_ty = dyn_cast<PointerType>(arg_type)) {
      // If the pointer passed points to something
      if (pointsToMap.find(passedArgs[arg_ct]) != pointsToMap.end()) {
        // Do book keeping for tracking what the new pointer
        // points to (the value passed to it)
        // Don't need to create a new Z3 variable until
        // it is dereferenced
        std::string arg_name = passedArgs[arg_ct];
        PointsTo *temp = new PointsTo;
        temp->name = pointsToMap[arg_name]->name;
        temp->isArray = pointsToMap[arg_name]->isArray;
        temp->arrayOffsetSymb = pointsToMap[arg_name]->arrayOffsetSymb;
        temp->symOffsetName = pointsToMap[arg_name]->symOffsetName;
        temp->concreteOffset = pointsToMap[arg_name]->concreteOffset;
        temp->arrayBitWidth = pointsToMap[arg_name]->arrayBitWidth;
        // Create a new variable for new pointer and update
        // pointsToMap
        std::string varName = CreateVarName(arg->getName().str());
        pointsToMap[varName] = temp;
      } else {
        print_error("GetInstConstraint Error: Function passed pointer "
                    "argument that is not in pointsToMap\n");
      }
    } else if (AllocaInst *ai = dyn_cast<AllocaInst>(arg)) {
      print_error("GetInstConstraint Error: unhandled function argument of "
                  "type Alloca\n");
    } else {
      print_error(
          "GetInstConstraint Error: unhandled function argument type\n");
    }
    arg_ct++;
  }
}

void GetCallInstConstraint(CallInst *ci, std::string *result) {

  print_error("GetInstConstraint: CallInst\n");
  Function *func = ci->getCalledFunction();
  // If function is not defined in the source files
  // (likely included from a library)
  if (func->isDeclaration()) {
    if (func->getName().str() == "atoi") {
      GetAtoiInstConstraint(ci, result);
    } else if (func->getName().str() == "calloc") {
      GetCallocInstConstraint(ci, result);
    } else if (func->getName().str() == "memset") {
      GetMemsetInstConstraint(ci, result);
    } else if (func->getName().str() == "pow") {
      GetPowInstConstraint(ci, result);
    } else if (func->getName().str() == "strlen") {
      GetStrlenInstConstraint(ci, result);
    } else if (func->getName().str() == "__isoc99_scanf") {
      GetScanfInstConstraint(ci, result);
    } else if (func->getName().str() == "printf") {
      // Printf has no impact on state, so ignore it
      (*result) = "";
    } else {
      print_error("GetInstConstraint Error: Unknown Function Call\n");
      ci->dump();
    }
  }
  // If the function is user defined
  else {
    GetUserFuncInstConstraint(ci, result);
  }
}

std::string GetInstConstraint(Instruction *inst, std::string prevBB,
                              std::string nextBB) {
  std::string result = "";

  if (BranchInst *bi = dyn_cast<BranchInst>(inst)) {
    GetBranchInstConstraint(bi, nextBB, &result);
  } else if (AllocaInst *ai = dyn_cast<AllocaInst>(inst)) {
    GetAllocaInstConstraint(ai, &result);
  } else if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(inst)) {
    GetGEPInstConstraint(gep, &result);
  } else if (StoreInst *si = dyn_cast<StoreInst>(inst)) {
    GetStoreInstConstraint(si, &result);
  } else if (LoadInst *li = dyn_cast<LoadInst>(inst)) {
    GetLoadInstConstraint(li, &result);
  } else if (BinaryOperator *bo = dyn_cast<BinaryOperator>(inst)) {
    GetBinaryOperatorConstraint(bo, &result);
  } else if (CmpInst *ci = dyn_cast<CmpInst>(inst)) {
    GetCmpInstConstraint(ci, &result);
  } else if (PHINode *pn = dyn_cast<PHINode>(inst)) {
    GetPHINodeConstraint(pn, prevBB, &result);
  } else if (SExtInst *si = dyn_cast<SExtInst>(inst)) {
    GetSExtInstConstraint(si, &result);
  } else if (TruncInst *ti = dyn_cast<TruncInst>(inst)) {
    GetTrunInstConstraint(ti, &result);
  } else if (ReturnInst *ri = dyn_cast<ReturnInst>(inst)) {
    GetReturnInstConstraint(ri, &result);
  } else if (CallInst *ci = dyn_cast<CallInst>(inst)) {
    GetCallInstConstraint(ci, &result);
  } else {
    print_error("GetInstConstraint Error: Unknown Instruction Type!\n");
    inst->dump();
  }

  return result;
}

// Get the Z3 constraints the encode the behavior of the
// program path being modeled
std::vector<std::string> GetTraceConstraints(
    std::map<std::string, std::map<std::string, CFGNode *> > *FunctionCFGMap,
    std::vector<Instruction *> trace) {

  // vector to return constraints
  std::vector<std::string> result;

  // Symbol table for looking up current version of a variable (similar to SSA
  // form but LLVM doesn't always work well
  // with loops for this). This is mostly to deal with the presence of loops
  // std::map<std::string, int> VarSymbolTable;

  // push the main state on the stateStack
  stateStack.push(new State);

  // Start of python z3 python script
  result.push_back("from z3 import *\n");
  result.push_back("import " + model_library_name + " as " +
                   model_library_prefix + "\n");
  result.push_back("g = Goal()\n\n");

  std::string currBB, prevBB, nextBB, currFunc;

  int pythonStmtCt = 0;

  // For each instruction in inlined trace
  for (int i = 0; i < trace.size(); i++) {

    currBB = trace[i]->getParent()->getName().str();
    currFunc = trace[i]->getParent()->getParent()->getName().str();

    // Find the prev bb in trace
    for (int j = i; j >= 0; j--) {
      std::string bbName = trace[j]->getParent()->getName().str();
      std::string funcName =
          trace[j]->getParent()->getParent()->getName().str();
      if (bbName != currBB && currFunc == funcName) {
        prevBB = bbName;
        break;
      }
    }

    // Find the next BB in trace
    for (int j = i; j < trace.size(); j++) {
      std::string bbName = trace[j]->getParent()->getName().str();
      std::string funcName =
          trace[j]->getParent()->getParent()->getName().str();
      if (bbName != currBB && currFunc == funcName) {
        nextBB = bbName;
        break;
      }
    }

    // Get the current instructions constraints
    std::string instConst = GetInstConstraint(trace[i], prevBB, nextBB);

    if (instConst != "") {
      llvm::errs() << "'''\n";
      trace[i]->dump();
      llvm::errs() << "'''\n";
      llvm::errs() << instConst << "\n\n";
      result.push_back(instConst);
    }
  }

  return result;
}

// Get a vector of the instructions executed on the path being
// modeled (in the order they are executed)
std::vector<Instruction *> GetInlinedInstructionOrder(
    std::vector<std::string> &bb_trace,
    std::map<std::string, std::map<std::string, CFGNode *> > &FunctionCFGMap) {

  std::vector<Instruction *> result;

  int curr_bb_idx = 0;

  // Stack used for tracking w
  std::stack<std::pair<std::string, int> > bb_stack;

  // push the first bb on the stack
  bb_stack.push(std::pair<std::string, int>(bb_trace[curr_bb_idx], 0));

  // Build a list containt the order of BB's executed
  std::vector<std::string> temp;
  for (int i = 0; i < bb_trace.size(); i++) {
    temp.push_back(bb_trace[i] + "*" + std::to_string(i));
  }
  bb_trace = temp;

  // Keep track of what BBs have already started execution
  // (used to handle function calls)
  std::map<std::string, bool> AlreadyStartedMap;
  for (int i = 0; i < bb_trace.size(); i++) {
    AlreadyStartedMap[bb_trace[i]] = false;
  }

  while (!bb_stack.empty()) {

    // Get the instruction set of the basic block currently
    // being executed in the trace and find the next
    // instruction that was executed in the trace
    std::string curr_bb = bb_stack.top().first;
    int inst_loc = bb_stack.top().second;
    size_t funcNameEnds = curr_bb.find("_");
    std::string func_name = curr_bb.substr(0, funcNameEnds);
    std::vector<Instruction *> instructions =
        FunctionCFGMap[func_name][curr_bb.substr(0, curr_bb.find("*"))]
            ->instructions;

    // If starting at the beginning of a BB increment
    // the BB counter
    if (!AlreadyStartedMap[bb_stack.top().first]) {
      curr_bb_idx++;
    }

    Instruction *inst;
    // Increment till the end of the BB's instructions
    // or till a function call or return occurs
    for (; inst_loc < instructions.size(); inst_loc++) {
      inst = instructions[inst_loc];
      if (CallInst *ci = dyn_cast<CallInst>(inst)) {
        if (ci->getCalledFunction()->isDeclaration()) {
          result.push_back(inst);
        } else {
          result.push_back(inst);
          break;
        }
      } else {
        result.push_back(inst);
      }
    }

    // If a call inst occurs remember where we left
    // off in the BB that makes the call and push the
    // new BB on the stack
    if (CallInst *ci = dyn_cast<CallInst>(inst)) {
      bb_stack.top().second = inst_loc + 1;
      bb_stack.push(std::pair<std::string, int>(bb_trace[curr_bb_idx], 0));
    }
    // If a return occurs pop off the last BB of current function
    // being executed in the trace
    else if (ReturnInst *ri = dyn_cast<ReturnInst>(inst)) {
      bb_stack.pop();
    }
    // If the BB compeletes
    else {
      bb_stack.pop();
      bb_stack.push(std::pair<std::string, int>(bb_trace[curr_bb_idx], 0));
    }

    // mark the current BB as being started
    AlreadyStartedMap[curr_bb] = true;
  }

  return result;
}

// Create the Z3Py file that generates a SAT formula
// (in Z3's format) of the path in the program's
// execution
void CreateZ3PyFile(std::vector<std::string> result) {

  std::ofstream z3_file(Z3Filename);

  // Write each constraint to the file that
  // encodes the behavior of the path
  // being modeled
  for (int i = 0; i < result.size(); i++) {
    z3_file << result[i];
  }
  z3_file << "\n";

  // Add code to the Z3Py file that bit-blasts the SMT formula,
  // and then prints its corresponding SAT formula (in Z3's
  // internal SAT format)
  z3_file << "t = Then('simplify', 'bit-blast', 'tseitin-cnf')\n";
  z3_file << "subgoal = t(g)\n";
  z3_file << "assert len(subgoal) == 1\n";
  z3_file << "print subgoal[0].sexpr()\n";

  z3_file.close();
}

namespace {
struct Hello2 : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  Hello2() : ModulePass(ID) {}

  bool runOnModule(Module &m) override {

    std::map<std::string, std::map<std::string, CFGNode *> > FunctionCFGMap;

    // Create global pointer to the module to avoid
    // expenseive parameter passing
    mod_ptr = &m;

    // Get the trace being modeled
    std::vector<std::string> bb_trace = get_trace();

    // Change names of bbs, instructions and parameters
    // (makes debugging easier)
    rename_bbs();
    rename_insts();
    rename_func_params();
    get_bounds();

    // Build a nested map for looking up BB's corresponding CFGNode
    // For ex. to find the CFG for bb1 in func1 use: FunctionCFGMap[func1][bb1]
    BuildFunctionCFGMap(&FunctionCFGMap);

    // Get a vector of the instructions executed on the path being
    // modeled (in the order they are executed)
    std::vector<Instruction *> instructionOrder =
        GetInlinedInstructionOrder(bb_trace, FunctionCFGMap);

    // Get the Z3 constraints the encode the behavior of the
    // program path being modeled
    std::vector<std::string> result =
        GetTraceConstraints(&FunctionCFGMap, instructionOrder);

    return false;
  }

  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    // AU.setPreservesAll();
  }
};
}

char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("CFCountPass",
  "Pass for generating a Z3 SAT representation of a program's execution path");
