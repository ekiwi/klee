//===-- ExprUCLID5Printer.h ------------------------------------------*- C++
//-*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXPRUCLID5PRINTER_H
#define KLEE_EXPRUCLID5PRINTER_H

#include <string>
#include <set>
#include <map>
#include <klee/Constraints.h>
#include <klee/Expr.h>
#include <klee/util/PrintContext.h>
#include <klee/Solver.h>

namespace llvm {
class raw_ostream;
}

namespace klee {

class ExprUCLID5Printer {
public:
  /// Create a new printer that will print a UCLID5 program.
  ExprUCLID5Printer(const Query &q, llvm::raw_ostream &output);

  ~ExprUCLID5Printer();

  // Print symbolic inputs
  void printArrayDeclarations();

  void printPathConditions(const std::string& name);

  void printExpr(const std::string& name);

protected:
  enum SMTLIB_SORT { SORT_BITVECTOR, SORT_BOOL };

  /// Contains the arrays found during scans
  std::set<const Array *> usedArrays;

  /// Set of expressions seen during scan.
  std::set<ref<Expr> > seenExprs;

  typedef std::map<const ref<Expr>, int> BindingMap;

  /// Let expression binding number map. Under the :named abbreviation mode,
  /// negative binding numbers indicate that the abbreviation has already been
  /// emitted, so it may be used.
  BindingMap bindings;

  /// An ordered list of expression bindings.
  /// Exprs in BindingMap at index i depend on Exprs in BindingMap at i-1.
  /// Exprs in orderedBindings[0] have no dependencies.
  std::vector<BindingMap> orderedBindings;

  /// Output stream to write to
  llvm::raw_ostream *o;

  /// The query to print
  const Query *query;

  /// Determine the SMTLIBv2 sort of the expression
  SMTLIB_SORT getSort(const ref<Expr> &e);

  /// Print an expression but cast it to a particular SMTLIBv2 sort first.
  void printCastToSort(const ref<Expr> &e, ExprUCLID5Printer::SMTLIB_SORT sort);

  // Resets various internal objects for a new query
  void reset();

  // Scan all constraints and the query
  void scanAll();

  // Print an initial SMTLIBv2 comment before anything else is printed
  void printNotice();

  // Print SMTLIBv2 options e.g. (set-option :option-name <value>) command
  void printOptions();

  // Print SMTLIBv2 logic to use e.g. (set-logic QF_ABV)
  void printSetLogic();

  // Print SMTLIBv2 for the query optimised for human readability
  void printHumanReadableQuery();

  // Print SMTLIBv2 for the query optimised for minimal query size.
  // This does not imply ABBR_LET or ABBR_NAMED (although it would be wise
  // to use them to minimise the query size further)
  void printMachineReadableQuery();

  void printQueryInSingleAssert();

  /// Print the SMTLIBv2 command to check satisfiability and also optionally
  /// request for values
  /// \sa setArrayValuesToGet()
  void printAction();

  /// Print the SMTLIBv2 command to exit
  void printExit();

  /// Print a Constant in the format specified by the current "Constant Display
  /// Mode"
  void printConstant(const ref<ConstantExpr> &e);

  /// Recursively print expression
  /// \param e is the expression to print
  /// \param expectedSort is the sort we want. If "e" is not of the right type a
  /// cast will be performed.
  /// \param abbrMode the abbreviation mode to use for this expression
  void printExpression(const ref<Expr> &e, SMTLIB_SORT expectedSort);

  /// Scan Expression recursively for Arrays in expressions. Found arrays are
  /// added to
  /// the usedArrays vector.
  void scan(const ref<Expr> &e);

  /// Scan bindings for expression intra-dependencies. The result is written
  /// to the orderedBindings vector that is later used for nested expression
  /// printing in the let abbreviation mode.
  void scanBindingExprDeps();

  /* Rules of recursion for "Special Expression handlers" and
   *printSortArgsExpr()
   *
   * 1. The parent of the recursion will have created an indent level for you so
   *you don't need to add another initially.
   * 2. You do not need to add a line break (via printSeperator() ) at the end,
   *the parent caller will handle that.
   * 3. The effect of a single recursive call should not affect the depth of the
   *indent stack (nor the contents
   *    of the indent stack prior to the call). I.e. After executing a single
   *recursive call the indent stack
   *    should have the same size and contents as before executing the recursive
   *call.
   */

  // Special Expression handlers
  void printReadExpr(const ref<ReadExpr> &e);
  void printExtractExpr(const ref<ExtractExpr> &e);
  void printCastExpr(const ref<CastExpr> &e);
  void printNotEqualExpr(const ref<NeExpr> &e);
  void printSelectExpr(const ref<SelectExpr> &e,
                               ExprUCLID5Printer::SMTLIB_SORT s);
  void printAShrExpr(const ref<AShrExpr> &e);

  // For the set of operators that take sort "s" arguments
  void printSortArgsExpr(const ref<Expr> &e,
                                 ExprUCLID5Printer::SMTLIB_SORT s);

  /// For the set of operators that come in two sorts (e.g. (and () ()) (bvand
  /// () ()) )
  /// These are and,xor,or,not
  /// \param e the Expression to print
  /// \param s the sort of the expression we want
  void printLogicalOrBitVectorExpr(const ref<Expr> &e,
                                           ExprUCLID5Printer::SMTLIB_SORT s);

  /// Recursively prints updatesNodes
  void printUpdatesAndArray(const UpdateNode *un, const Array *root);

  /// This method does the translation between Expr classes and SMTLIBv2
  /// keywords
  /// \return A C-string of the SMTLIBv2 keyword
  const char *getSMTLIBKeyword(const ref<Expr> &e);

  void printSeperator();

  /// Helper function for scan() that scans the expressions of an update node
  void scanUpdates(const UpdateNode *un);

  /// Helper printer class
  PrintContext *p;

  /// This contains the query from the solver but negated for our purposes.
  /// \sa negateQueryExpression()
  ref<Expr> queryAssert;

  /// Indicates if there were any constant arrays founds during a scan()
  bool haveConstantArray;

private:
  /// Print expression without top-level abbreviations
  void printFullExpression(const ref<Expr> &e, SMTLIB_SORT expectedSort);

  /// Print an assert statement for the given expr.
  void printAssert(const ref<Expr> &e);

  // Pointer to a vector of Arrays. These will be used for the (get-value () )
  // call.
  const std::vector<const Array *> *arraysToCallGetValueOn;
};
}

#endif
