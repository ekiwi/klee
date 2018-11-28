//===-- ExprUCLID5Printer.cpp -----------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "klee/util/ExprUCLID5Printer.h"

#include <stack>

namespace klee {

ExprUCLID5Printer::ExprUCLID5Printer(const Query &q, llvm::raw_ostream &output)
{
  query = &q;
  scanAll();

  o = &output;
  p = new PrintContext(output);
}

ExprUCLID5Printer::~ExprUCLID5Printer() {
  if(p != nullptr) { delete p; }
}


void ExprUCLID5Printer::printPathConditions(const std::string& name) {
  unsigned int count = 0;
  for(auto cc : query->constraints) {
    *p << name << "_" << count << " = ";
    printExpression(cc, SORT_BOOL);
    *p << ";\n";
    count += 1;
  }
  *p << name << " = ";
  if(count == 0) { *p << "true"; }
  else if(count == 1) { *p << name << "_0"; }
  else {
    *p << name << "_0";
    for(unsigned int ii = 1; ii < count; ii++) {
      *p << " && " << name << "_" << ii;
    }
  }
  *p << ";\n";
}

void ExprUCLID5Printer::printExpr(const std::string& name) {
  const auto sort = getSort(query->expr);
  *p << name << " = ";
  printExpression(query->expr, sort);
  *p << ";\n";
}

void ExprUCLID5Printer::printConstant(const ref<ConstantExpr> &e) {
  // boolean constants
  if (e->isTrue()) {
    *p << "true";
    return;
  }
  if (e->isFalse()) {
    *p << "false";
    return;
  }

  // bit vector constants
  std::string value;
  e->toString(value, 10);
  *p << value << "bv" << e->getWidth();
}

void ExprUCLID5Printer::printExpression(
  const ref<Expr> &e, ExprUCLID5Printer::SMTLIB_SORT expectedSort) {
  // check if casting might be necessary
  if (getSort(e) != expectedSort) {
    printCastToSort(e, expectedSort);
    return;
  }

  BindingMap::iterator i = bindings.find(e);
  if (i != bindings.end()) {
    *p << "?B" << i->second;
    return;
  }

  printFullExpression(e, expectedSort);
}

void ExprUCLID5Printer::printFullExpression(
    const ref<Expr> &e, ExprUCLID5Printer::SMTLIB_SORT expectedSort) {
  switch (e->getKind()) {
  case Expr::Constant:
    printConstant(cast<ConstantExpr>(e));
    return; // base case

  case Expr::NotOptimized:
    // skip to child
    printExpression(e->getKid(0), expectedSort);
    return;

  case Expr::Read:
    printReadExpr(cast<ReadExpr>(e));
    return;

  case Expr::Extract:
    printExtractExpr(cast<ExtractExpr>(e));
    return;

  case Expr::SExt:
  case Expr::ZExt:
    printCastExpr(cast<CastExpr>(e));
    return;

  case Expr::Select:
    // the if-then-else expression.
    printSelectExpr(cast<SelectExpr>(e), expectedSort);
    return;

  case Expr::Eq:
  case Expr::Ne:
    /* The "=" and distinct operators are special in that it can take any sort
     * but we must enforce that both arguments are the same sort. We do this in
     * a lazy way by enforcing the second argument is of the same type as the
     * first.
     */
    printSortArgsExpr(e, getSort(e->getKid(0)));
    return;

  case Expr::And:
  case Expr::Or:
  case Expr::Xor:
  case Expr::Not:
    printLogicalOrBitVectorExpr(e, expectedSort);
    return;

  case Expr::AShr:
    printAShrExpr(cast<AShrExpr>(e));
    return;

  default:
    printSortArgsExpr(e, SORT_BITVECTOR);
    return;
  }
}

void ExprUCLID5Printer::printReadExpr(const ref<ReadExpr> &e) {
  *p << "(" << getSMTLIBKeyword(e) << " ";
  p->pushIndent();

  p->write(" ");

  // print array with updates recursively
  printUpdatesAndArray(e->updates.head, e->updates.root);

  // print index
  p->write(" ");
  printExpression(e->index, SORT_BITVECTOR);

  p->popIndent();
  p->write(" ");
  *p << ")";
}

void ExprUCLID5Printer::printExtractExpr(const ref<ExtractExpr> &e) {
  unsigned int lowIndex = e->offset;
  unsigned int highIndex = lowIndex + e->width - 1;

  *p << "((_ " << getSMTLIBKeyword(e) << " " << highIndex << "  " << lowIndex
     << ") ";

  p->pushIndent(); // add indent for recursive call
  p->write(" ");

  // recurse
  printExpression(e->getKid(0), SORT_BITVECTOR);

  p->popIndent(); // pop indent added for the recursive call
  p->write(" ");
  *p << ")";
}

void ExprUCLID5Printer::printCastExpr(const ref<CastExpr> &e) {
  /* sign_extend and zero_extend behave slightly unusually in SMTLIBv2,
   * instead of specifying of what bit-width we would like to extend to
   * we specify how many bits to add to the child expression
   *
   * e.g
   * ((_ sign_extend 64) (_ bv5 32))
   *
   * gives a (_ BitVec 96) instead of (_ BitVec 64)
   *
   * So we must work out how many bits we need to add.
   *
   * (e->width) is the desired number of bits
   * (e->src->getWidth()) is the number of bits in the child
   */
  unsigned int numExtraBits = (e->width) - (e->src->getWidth());

  *p << "((_ " << getSMTLIBKeyword(e) << " " << numExtraBits << ") ";

  p->pushIndent(); // add indent for recursive call
  p->write(" ");

  // recurse
  printExpression(e->src, SORT_BITVECTOR);

  p->popIndent(); // pop indent added for recursive call
  p->write(" ");

  *p << ")";
}

void ExprUCLID5Printer::printAShrExpr(const ref<AShrExpr> &e) {
  // There is a difference between AShr and SMT-LIBv2's
  // bvashr function when the shift amount is >= the bit width
  // so we need to treat it specially here.
  //
  // Technically this is undefined behaviour for LLVM's ashr operator
  // but currently llvm::APInt:ashr(...) will emit 0 if the shift amount
  // is >= the bit width but this does not match how SMT-LIBv2's bvashr
  // behaves as demonstrates by the following query
  //
  // (declare-fun x () (_ BitVec 32))
  // (declare-fun y () (_ BitVec 32))
  // (declare-fun result () (_ BitVec 32))
  // (assert (bvuge y (_ bv32 32)))
  // (assert (= result (bvashr x y)))
  // (assert (distinct (_ bv0 32) result))
  // (check-sat)
  // sat
  //
  // Our solution is to instead emit
  //
  // (ite (bvuge shift_amount bit_width)
  //      (_ bv0 bitwidth)
  //      (bvashr value_to_shift shift_amount)
  // )
  //

  Expr::Width bitWidth = e->getKid(0)->getWidth();
  assert(bitWidth > 0 && "Invalid bit width");
  ref<Expr> bitWidthExpr = ConstantExpr::create(bitWidth, bitWidth);
  ref<Expr> zeroExpr = ConstantExpr::create(0, bitWidth);

  // FIXME: we print e->getKid(1) twice and it might not get
  // abbreviated
  *p << "(ite";
  p->pushIndent();
  p->write(" ");

  *p << "(bvuge";
  p->pushIndent();
  p->write(" ");
  printExpression(e->getKid(1), SORT_BITVECTOR);
  p->write(" ");
  printExpression(bitWidthExpr, SORT_BITVECTOR);
  p->popIndent();
  p->write(" ");
  *p << ")";

  p->write(" ");
  printExpression(zeroExpr, SORT_BITVECTOR);
  p->write(" ");

  *p << "(bvashr";
  p->pushIndent();
  p->write(" ");
  printExpression(e->getKid(0), SORT_BITVECTOR);
  p->write(" ");
  printExpression(e->getKid(1), SORT_BITVECTOR);
  p->popIndent();
  p->write(" ");
  *p << ")";

  p->popIndent();
  p->write(" ");
  *p << ")";
}

const char *ExprUCLID5Printer::getSMTLIBKeyword(const ref<Expr> &e) {

  switch (e->getKind()) {
  case Expr::Read:
    return "select";
  case Expr::Select:
    return "ite";
  case Expr::Concat:
    return "concat";
  case Expr::Extract:
    return "extract";
  case Expr::ZExt:
    return "zero_extend";
  case Expr::SExt:
    return "sign_extend";

  case Expr::Add:
    return "bvadd";
  case Expr::Sub:
    return "bvsub";
  case Expr::Mul:
    return "bvmul";
  case Expr::UDiv:
    return "bvudiv";
  case Expr::SDiv:
    return "bvsdiv";
  case Expr::URem:
    return "bvurem";
  case Expr::SRem:
    return "bvsrem";

  /* And, Xor, Not and Or are not handled here because there different versions
   * for different sorts. See printLogicalOrBitVectorExpr()
   */

  case Expr::Shl:
    return "bvshl";
  case Expr::LShr:
    return "bvlshr";
  // AShr is not supported here. See printAShrExpr()

  case Expr::Eq:
    return "=";
  case Expr::Ne:
    return "distinct";

  case Expr::Ult:
    return "bvult";
  case Expr::Ule:
    return "bvule";
  case Expr::Ugt:
    return "bvugt";
  case Expr::Uge:
    return "bvuge";

  case Expr::Slt:
    return "bvslt";
  case Expr::Sle:
    return "bvsle";
  case Expr::Sgt:
    return "bvsgt";
  case Expr::Sge:
    return "bvsge";

  default:
    llvm_unreachable("Conversion from Expr to SMTLIB keyword failed");
  }
}

void ExprUCLID5Printer::printUpdatesAndArray(const UpdateNode *un,
                                             const Array *root) {
  if (un != nullptr) {
    *p << "(store ";
    p->pushIndent();
    p->write(" ");

    // recurse to get the array or update that this store operations applies to
    printUpdatesAndArray(un->next, root);

    p->write(" ");

    // print index
    printExpression(un->index, SORT_BITVECTOR);
    p->write(" ");

    // print value that is assigned to this index of the array
    printExpression(un->value, SORT_BITVECTOR);

    p->popIndent();
    p->write(" ");
    *p << ")";
  } else {
    // The base case of the recursion
    *p << root->name;
  }
}

void ExprUCLID5Printer::scanAll() {
  // perform scan of all expressions
  for (auto ii : query->constraints) {
    scan(ii);
  }
  // Scan the query too
  scan(query->expr);
  // Scan bindings for expression intra-dependencies
  scanBindingExprDeps();
}

namespace {

struct ArrayPtrsByName {
  bool operator()(const Array *a1, const Array *a2) const {
    return a1->name < a2->name;
  }
};

}

void ExprUCLID5Printer::printArrayDeclarations() {
  // Assume scan() has been called

  // Declare arrays in a deterministic order.
  std::vector<const Array *> sortedArrays(usedArrays.begin(), usedArrays.end());
  std::sort(sortedArrays.begin(), sortedArrays.end(), ArrayPtrsByName());
  for (auto array : sortedArrays) {
    *o << "input " << array->name << " : [bv" << array->getDomain()
       << "]bv" << array->getRange() << ";\n";
  }

  // Set array values for constant values
  if (haveConstantArray) {

    const Array *array;

    // loop over found arrays
    for (std::vector<const Array *>::iterator it = sortedArrays.begin();
         it != sortedArrays.end(); it++) {
      array = *it;
      int byteIndex = 0;
      if (array->isConstantArray()) {
        /*loop over elements in the array and generate an assert statement
          for each one
         */
        for (std::vector<ref<ConstantExpr> >::const_iterator
                 ce = array->constantValues.begin();
             ce != array->constantValues.end(); ce++, byteIndex++) {
          *p << "TODO: generate an assume!\n";
          *p << "(assert (";
          p->pushIndent();
          *p << "= ";
          p->pushIndent();
          p->write(" ");

          *p << "(select " << array->name << " (_ bv" << byteIndex << " "
             << array->getDomain() << ") )";
          p->write(" ");
          printConstant((*ce));

          p->popIndent();
          p->write(" ");
          *p << ")";
          p->popIndent();
          p->write(" ");
          *p << ")";

          p->breakLineI();
        }
      }
    }
  }
}


void ExprUCLID5Printer::printQueryInSingleAssert() {
  // We negate the Query Expr because in KLEE queries are solved
  // in terms of validity, but SMT-LIB works in terms of satisfiability
  ref<Expr> queryAssert = Expr::createIsZero(query->expr);

  // Print constraints inside the main query to reuse the Expr bindings
  for (std::vector<ref<Expr> >::const_iterator i = query->constraints.begin(),
                                               e = query->constraints.end();
       i != e; ++i) {
    queryAssert = AndExpr::create(queryAssert, *i);
  }

  // print just a single (assert ...) containing entire query
  printAssert(queryAssert);
}


void ExprUCLID5Printer::scan(const ref<Expr> &e) {
  assert(!(e.isNull()) && "found nullptr expression");

  if (isa<ConstantExpr>(e))
    return; // we don't need to scan simple constants

  if (seenExprs.insert(e).second) {
    // We've not seen this expression before

    if (const ReadExpr *re = dyn_cast<ReadExpr>(e)) {

      if (usedArrays.insert(re->updates.root).second) {
        // Array was not recorded before

        // check if the array is constant
        if (re->updates.root->isConstantArray()) {
          haveConstantArray = true;
        }

        // scan the update list
        scanUpdates(re->updates.head);
      }
    }

    // recurse into the children
    Expr *ep = e.get();
    for (unsigned int i = 0; i < ep->getNumKids(); i++) {
      scan(ep->getKid(i));
    }
  } else {
    // Add the expression to the binding map. The semantics of std::map::insert
    // are such that it will not be inserted twice.
    bindings.insert(std::make_pair(e, bindings.size()+1));
  }
}

void ExprUCLID5Printer::scanBindingExprDeps() {
  if (!bindings.size())
    return;

  // Mutual dependency storage
  typedef std::map<const ref<Expr>, std::set<ref<Expr> > > ExprDepMap;

  // A map from binding Expr (need abbreviating) "e" to the set of binding Expr
  // that are sub expressions of "e" (i.e. "e" uses these sub expressions).
  // usesSubExprMap[a].count(b) == 1  means that binding Expr "a" uses
  // sub Expr "b" (also a binding Expr).
  // One can think of this map representing the "depends on" edges
  // in a "dependency graph" where nodes are binding Expr roots
  ExprDepMap usesSubExprMap;

  // A map from Binding Expr "e" to the set of binding Expr that use "e"
  // subExprOfMap[a].count(b) == 1 means that binding Expr "a" is a sub Expr
  // of binding Expr "b".
  // One can think of this map as representing the edges in the previously
  // mentioned "dependency graph" except the direction of the edges
  // have been reversed
  ExprDepMap subExprOfMap;

  // Working queue holding expressions with no dependencies
  std::vector<ref<Expr> > nonDepBindings;

  // Iterate over bindings and collect dependencies
  for (BindingMap::const_iterator it = bindings.begin();
       it != bindings.end(); ++it) {
    std::stack<ref<Expr> > childQueue;
    childQueue.push(it->first);
    // Non-recursive expression parsing
    while (childQueue.size()) {
      Expr *ep = childQueue.top().get();
      childQueue.pop();
      for (unsigned i = 0; i < ep->getNumKids(); ++i) {
        ref<Expr> e = ep->getKid(i);
        if (isa<ConstantExpr>(e))
          continue;
        // Are there any dependencies in the bindings?
        if (bindings.count(e)) {
          usesSubExprMap[it->first].insert(e);
          subExprOfMap[e].insert(it->first);
        } else {
          childQueue.push(e);
        }
      }
    }
    // Store expressions with zero deps
    if (!usesSubExprMap.count(it->first))
      nonDepBindings.push_back(it->first);
  }
  assert(nonDepBindings.size() && "there must be expr bindings with no deps");

  // Unroll the dependency tree starting with zero-dep expressions
  // and redefine bindings
  unsigned counter = 1;
  // nonDepBindings always holds expressions with no dependencies
  while (nonDepBindings.size()) {
    BindingMap levelExprs;
    std::vector<ref<Expr> > tmp(nonDepBindings);
    nonDepBindings.clear();
    for (std::vector<ref<Expr> >::const_iterator nonDepExprIt = tmp.begin();
         nonDepExprIt != tmp.end(); ++nonDepExprIt) {
      // Save to the level expression bindings
      levelExprs.insert(std::make_pair(*nonDepExprIt, counter++));
      // Who is dependent on me?
      ExprDepMap::iterator depsIt = subExprOfMap.find(*nonDepExprIt);
      if (depsIt != subExprOfMap.end()) {
        for (std::set<ref<Expr> >::iterator exprIt = depsIt->second.begin();
             exprIt != depsIt->second.end(); ) {
          // Erase dependency
          ExprDepMap::iterator subExprIt = usesSubExprMap.find(*exprIt);
          assert(subExprIt != usesSubExprMap.end());
          assert(subExprIt->second.count(*nonDepExprIt));
          subExprIt->second.erase(*nonDepExprIt);
          // If the expression *exprIt does not have any
          // dependencies anymore, add it to the queue
          if (!subExprIt->second.size()) {
            nonDepBindings.push_back(*exprIt);
            depsIt->second.erase(exprIt++);
          } else {
            ++exprIt;
          }
        }
      }
    }
    // Store level bindings
    orderedBindings.push_back(levelExprs);
  }
}

void ExprUCLID5Printer::scanUpdates(const UpdateNode *un) {
  while (un != nullptr) {
    scan(un->index);
    scan(un->value);
    un = un->next;
  }
}

void ExprUCLID5Printer::printAssert(const ref<Expr> &e) {
  p->pushIndent();
  *p << "(assert";
  p->pushIndent();
  p->write(" ");

  if (orderedBindings.size() != 0) {
    // Only print let expression if we have bindings to use.
    *p << "(let";
    p->pushIndent();
    p->write(" ");
    *p << "(";
    p->pushIndent();

    // Clear original bindings, we'll be using orderedBindings
    // to print nested let expressions
    bindings.clear();

    // Print each binding on its level
    for (unsigned i = 0; i < orderedBindings.size(); ++i) {
      BindingMap levelBindings = orderedBindings[i];
      for (BindingMap::const_iterator j = levelBindings.begin();
           j != levelBindings.end(); ++j) {
        p->write(" ");
        *p << "(?B" << j->second;
        p->pushIndent();
        p->write(" ");

        // We can abbreviate SORT_BOOL or SORT_BITVECTOR in let expressions
        printExpression(j->first, getSort(j->first));

        p->popIndent();
        p->write(" ");
        *p << ")";
      }
      p->popIndent();
      p->write(" ");
      *p << ")";
      p->write(" ");

      // Add nested let expressions (if any)
      if (i < orderedBindings.size()-1) {
        *p << "(let";
        p->pushIndent();
        p->write(" ");
        *p << "(";
        p->pushIndent();
      }
      // Insert current level bindings so that they can be used
      // in the next level during expression printing
      bindings.insert(levelBindings.begin(), levelBindings.end());
    }

    printExpression(e, SORT_BOOL);

    for (unsigned i = 0; i < orderedBindings.size(); ++i) {
      p->popIndent();
      p->write(" ");
      *p << ")";
    }
  } else {
    printExpression(e, SORT_BOOL);
  }

  p->popIndent();
  p->write(" ");
  *p << ")";
  p->popIndent();
  p->breakLineI();
}

ExprUCLID5Printer::SMTLIB_SORT ExprUCLID5Printer::getSort(const ref<Expr> &e) {
  switch (e->getKind()) {
  case Expr::NotOptimized:
    return getSort(e->getKid(0));

  // The relational operators are bools.
  case Expr::Eq:
  case Expr::Ne:
  case Expr::Slt:
  case Expr::Sle:
  case Expr::Sgt:
  case Expr::Sge:
  case Expr::Ult:
  case Expr::Ule:
  case Expr::Ugt:
  case Expr::Uge:
    return SORT_BOOL;

  // These may be bitvectors or bools depending on their width (see
  // printConstant and printLogicalOrBitVectorExpr).
  case Expr::Constant:
  case Expr::And:
  case Expr::Not:
  case Expr::Or:
  case Expr::Xor:
    return e->getWidth() == Expr::Bool ? SORT_BOOL : SORT_BITVECTOR;

  // Everything else is a bitvector.
  default:
    return SORT_BITVECTOR;
  }
}

void ExprUCLID5Printer::printCastToSort(const ref<Expr> &e,
                                        ExprUCLID5Printer::SMTLIB_SORT sort) {
  switch (sort) {
  case SORT_BITVECTOR:
    // We assume the e is a bool that we need to cast to a bitvector sort.
    *p << "(if(";
    printExpression(e, SORT_BOOL);
    p->write(") then 1bv1 else 0bv1)");
    break;
  case SORT_BOOL: {
    /* We make the assumption (might be wrong) that any bitvector whose unsigned
     * decimal value is zero is interpreted as "false", otherwise it is
     * true.
     *
     * This may not be the interpretation we actually want!
     */
    Expr::Width bitWidth = e->getWidth();
    *p << "(";
    printExpression(e, SORT_BITVECTOR);
    p->write(" == ");
    *p << "0bv" << bitWidth << ")";

    if (bitWidth != Expr::Bool) {
      llvm::errs()
          << "ExprUCLID5Printer : Warning. Casting a bitvector (length "
          << bitWidth << ") to bool!\n";
    }
    break;
  }
  }
}

void ExprUCLID5Printer::printSelectExpr(const ref<SelectExpr> &e,
                                        ExprUCLID5Printer::SMTLIB_SORT s) {
  // This is the if-then-else expression

  *p << "(" << getSMTLIBKeyword(e) << " ";
  p->pushIndent(); // add indent for recursive call

  // The condition
  p->write(" ");
  printExpression(e->getKid(0), SORT_BOOL);

  /* This operator is special in that the remaining children
   * can be of any sort.
   */

  // if true
  p->write(" ");
  printExpression(e->getKid(1), s);

  // if false
  p->write(" ");
  printExpression(e->getKid(2), s);

  p->popIndent(); // pop indent added for recursive call
  p->write(" ");
  *p << ")";
}

void ExprUCLID5Printer::printSortArgsExpr(const ref<Expr> &e,
                                          ExprUCLID5Printer::SMTLIB_SORT s) {
  *p << "(" << getSMTLIBKeyword(e) << " ";
  p->pushIndent(); // add indent for recursive call

  // loop over children and recurse into each expecting they are of sort "s"
  for (unsigned int i = 0; i < e->getNumKids(); i++) {
    p->write(" ");
    printExpression(e->getKid(i), s);
  }

  p->popIndent(); // pop indent added for recursive call
  p->write(" ");
  *p << ")";
}

void ExprUCLID5Printer::printLogicalOrBitVectorExpr(
    const ref<Expr> &e, ExprUCLID5Printer::SMTLIB_SORT s) {
  /* For these operators it is the case that the expected sort is the same as
   * the sorts
   * of the arguments.
   */

  *p << "(";
  switch (e->getKind()) {
  case Expr::And:
    *p << ((s == SORT_BITVECTOR) ? "bvand" : "and");
    break;
  case Expr::Not:
    *p << ((s == SORT_BITVECTOR) ? "bvnot" : "not");
    break;
  case Expr::Or:
    *p << ((s == SORT_BITVECTOR) ? "bvor" : "or");
    break;

  case Expr::Xor:
    *p << ((s == SORT_BITVECTOR) ? "bvxor" : "xor");
    break;
  default:
    llvm_unreachable("Conversion from Expr to SMTLIB keyword failed");
  }
  *p << " ";

  p->pushIndent(); // add indent for recursive call

  // loop over children and recurse into each expecting they are of sort "s"
  for (unsigned int i = 0; i < e->getNumKids(); i++) {
    p->write(" ");
    printExpression(e->getKid(i), s);
  }

  p->popIndent(); // pop indent added for recursive call
  p->write(" ");
  *p << ")";
}

}
