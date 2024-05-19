import heapq
import itertools
import random
from collections import defaultdict, Counter

import networkx as nx

from utils import remove_all, unique, first, probability, isnumber, issequence, Expr, expr, subexpressions, extend, infix_ops


class KB:
    """A knowledge base to which you can tell and ask sentences."""

    def __init__(self, sentence=None):
        if sentence:
            self.tell(sentence)

    def tell(self, sentence):
        """Add the sentence to the KB."""

        raise NotImplementedError

    def ask(self, query):
        """Return a substitution that makes the query true, or, failing that, return False."""
        return first(self.ask_generator(query), default=False)

    def ask_generator(self, query):
        """Yield all the substitutions that make query true."""
        raise NotImplementedError

    def retract(self, sentence):
        """Remove sentence from the KB."""
        raise NotImplementedError


class PropKB(KB):
    """A KB for propositional logic"""

    def __init__(self, sentence=None):
        super().__init__(sentence)
        self.clauses = []

    def tell(self, sentence):
        """Add the sentence's clauses to the KB."""
        self.clauses.extend(conjuncts(to_cnf(sentence)))

    def ask_generator(self, query):
        """Yield the empty substitution {} if KB entails query; else no results."""
        if tt_entails(Expr('&', *self.clauses), query):
            yield {}

    def ask_if_true(self, query):
        """Return True if the KB entails query, else return False."""
        for _ in self.ask_generator(query):
            return True
        return False

    def retract(self, sentence):
        """Remove the sentence's clauses from the KB."""
        for c in conjuncts(to_cnf(sentence)):
            if c in self.clauses:
                self.clauses.remove(c)


# ______________________________________________________________________________
#The following functions are for handling infix operators for implication and "OR" in logical expressions
infix_imp = '=>'

def expr_handle_infix_imp(x):
    x = x.replace(infix_imp, '==>')
    return x

infix_or = '\/'

def expr_handle_infix_or(x):
    x = x.replace(infix_or, '|')
    return x

#The following function converts each sentence in kb to the appropriate format and combines them into an expression
def kb2expr(kb):
    kb_expr = None
    for kb_sentence in kb:
        st = expr_handle_infix_imp(expr_handle_infix_or(kb_sentence))
        if kb_expr:
            kb_expr += '&' + '(' + st + ')'
        else:
            kb_expr = '(' + st + ')'
    return expr(kb_expr)

# ______________________________________________________________________________

def is_symbol(s):
    """A string s is a symbol if it starts with an alphabetic char."""
    return isinstance(s, str) and s[:1].isalpha()


def is_var_symbol(s):
    """A logic variable symbol is an initial-lowercase string."""
    return is_symbol(s) and s[0].islower()


def is_prop_symbol(s):
    """A proposition logic symbol is an initial-uppercase string."""
    return is_symbol(s) and (s[0].isupper() or s[0].islower())


def variables(s):
    """Return a set of the variables in expression s."""
    return {x for x in subexpressions(s) if is_variable(x)}


def is_definite_clause(s):
    """Returns True for exprs s of the form A & B & ... & C ==> D,
    where all literals are positive."""
    if is_symbol(s.op):
        return True
    elif s.op == '==>':
        antecedent, consequent = s.args
        return is_symbol(consequent.op) and all(is_symbol(arg.op) for arg in conjuncts(antecedent))
    else:
        return False

# ______________________________________________________________________________

def tt_entails(self, query):
  # Checks if the knowledge base entails the query using truth tables and counts the number of models.
  symbols = {x for clause in self.clauses for x in subexpressions(clause) if is_variable(x)}
  all_assignments = [{symbol: value for symbol, value in zip(symbols, truth_assignment)} for truth_assignment in itertools.product([True, False], repeat=len(symbols))]
  models = 0
  for assignment in all_assignments:
    all_true = True
    for clause in self.clauses: # Checks if all false, because if so then there's no need to count how many are true
      if not pl_true(clause, assignment):
        all_true = False
    if all_true:
      if not pl_true(query, assignment):
        return False
      else:
        models += 1  # Increment models counter
  return True, models



def tt_check_all(kb, alpha, symbols, model):
    """Auxiliary routine to implement tt_entails."""
    if not symbols:
        if pl_true(kb, model):
            result = pl_true(alpha, model)
            assert result in (True, False)
            return result
        else:
            return True
    else:
        P, rest = symbols[0], symbols[1:]
        return (tt_check_all(kb, alpha, rest, extend(model, P, True)) and
                tt_check_all(kb, alpha, rest, extend(model, P, False)))


def prop_symbols(x):
    """Return the set of all propositional symbols in x."""
    if not isinstance(x, Expr):
        return set()
    elif is_prop_symbol(x.op):
        return {x}
    else:
        return {symbol for arg in x.args for symbol in prop_symbols(arg)}

def pl_true(exp, model={}):
    """Return True if the propositional logic expression is true in the model,
    and False if it is false. If the model does not specify the value for
    every proposition, this may return None to indicate 'not obvious';
    this may happen even when the expression is tautological."""
    if exp in (True, False):
        return exp
    op, args = exp.op, exp.args
    if is_prop_symbol(op):
        return model.get(exp)
    elif op == '~':
        p = pl_true(args[0], model)
        if p is None:
            return None
        else:
            return not p
    elif op == '|':
        result = False
        for arg in args:
            p = pl_true(arg, model)
            if p is True:
                return True
            if p is None:
                result = None
        return result
    elif op == '&':
        result = True
        for arg in args:
            p = pl_true(arg, model)
            if p is False:
                return False
            if p is None:
                result = None
        return result
    p, q = args
    if op == '==>':
        return pl_true(~p | q, model)
    elif op == '<==':
        return pl_true(p | ~q, model)
    pt = pl_true(p, model)
    if pt is None:
        return None
    qt = pl_true(q, model)
    if qt is None:
        return None
    if op == '<=>':
        return pt == qt
    elif op == '^':  # xor or 'not equivalent'
        return pt != qt
    else:
        raise ValueError('Illegal operator in logic expression' + str(exp))


# ______________________________________________________________________________

# Convert to Conjunctive Normal Form (CNF)


def to_cnf(s):
    """Convert a propositional logical sentence to conjunctive normal form.
    That is, to the form ((A | ~B | ...) & (B | C | ...) & ...)"""
    s = expr(s)
    if isinstance(s, str):
        s = expr(s)
    s = eliminate_implications(s)  
    s = move_not_inwards(s)  
    return distribute_and_over_or(s)  


def eliminate_implications(s):
    """Change implications into equivalent form with only &, |, and ~ as logical operators."""
    s = expr(s)
    if not s.args or is_symbol(s.op):
        return s  
    args = list(map(eliminate_implications, s.args))
    a, b = args[0], args[-1]
    if s.op == '==>':
        return b | ~a
    elif s.op == '<==':
        return a | ~b
    elif s.op == '<=>':
        return (a | ~b) & (b | ~a)
    elif s.op == '^':
        assert len(args) == 2  
        return (a & ~b) | (~a & b)
    else:
        assert s.op in ('&', '|', '~')
        return Expr(s.op, *args)


def move_not_inwards(s):
    """Rewrite sentence s by moving negation sign inward."""
    s = expr(s)
    if s.op == '~':
        def NOT(b):
            return move_not_inwards(~b)

        a = s.args[0]
        if a.op == '~':
            return move_not_inwards(a.args[0])  
        if a.op == '&':
            return associate('|', list(map(NOT, a.args)))
        if a.op == '|':
            return associate('&', list(map(NOT, a.args)))
        return s
    elif is_symbol(s.op) or not s.args:
        return s
    else:
        return Expr(s.op, *list(map(move_not_inwards, s.args)))


def distribute_and_over_or(s):
    """Given a sentence s consisting of conjunctions and disjunctions
    of literals, return an equivalent sentence in CNF."""
    s = expr(s)
    if s.op == '|':
        s = associate('|', s.args)
        if s.op != '|':
            return distribute_and_over_or(s)
        if len(s.args) == 0:
            return False
        if len(s.args) == 1:
            return distribute_and_over_or(s.args[0])
        conj = first(arg for arg in s.args if arg.op == '&')
        if not conj:
            return s
        others = [a for a in s.args if a is not conj]
        rest = associate('|', others)
        return associate('&', [distribute_and_over_or(c | rest)
                               for c in conj.args])
    elif s.op == '&':
        return associate('&', list(map(distribute_and_over_or, s.args)))
    else:
        return s


def associate(op, args):
    """Given an associative op, return an expression with the same
    meaning as Expr(op, *args), but flattened -- that is, with nested
    instances of the same op promoted to the top level."""
    args = dissociate(op, args)
    if len(args) == 0:
        return _op_identity[op]
    elif len(args) == 1:
        return args[0]
    else:
        return Expr(op, *args)


_op_identity = {'&': True, '|': False, '+': 0, '*': 1}


def dissociate(op, args):
    """Given an associative op, return a flattened list result such
    that Expr(op, *result) means the same as Expr(op, *args)."""
    result = []

    def collect(subargs):
        for arg in subargs:
            if arg.op == op:
                collect(arg.args)
            else:
                result.append(arg)

    collect(args)
    return result


def conjuncts(s):
    """Return a list of the conjuncts in the sentence s."""
    return dissociate('&', [s])


def disjuncts(s):
    """Return a list of the disjuncts in the sentence s."""
    return dissociate('|', [s])

# ______________________________________________________________________________


class PropDefiniteKB(PropKB):
    """A KB of propositional definite clauses."""

    def tell(self, sentence):
        """Add a definite clause to this KB."""
        assert is_definite_clause(sentence), "Must be definite clause"
        self.clauses.append(sentence)

    def ask_generator(self, query):
        """Yield the empty substitution if KB implies query; else nothing."""
        if pl_fc_entails(self.clauses, query):
            yield {}

    def retract(self, sentence):
        self.clauses.remove(sentence)

    def clauses_with_premise(self, p):
        """Return a list of the clauses in KB that have p in their premise.
        This could be cached away for O(1) speed, but we'll recompute it."""
        return [c for c in self.clauses if c.op == '==>' and p in conjuncts(c.args[0])]
    
    def clauses_with_conclusion(self, q):
        """Return a list of the clauses in KB that have q as their conclusion."""
        return [c for c in self.clauses if c.op == '==>' and c.args[1] == q]
    

#This function represents the Forward Chaining (FC) Algorithm
def pl_fc_entails(kb, q):
    #Initialization of values
    count = {c: len(conjuncts(c.args[0])) for c in kb.clauses if c.op == '==>'}
    inferred = defaultdict(bool)
    agenda = list(reversed([s for s in kb.clauses if is_prop_symbol(s.op)]))
    entailed_symbols = []

    #Loop through each clause in the agenda
    while agenda:
        p = agenda.pop()
        if p == q:
            entailed_symbols.append(p)
            return True, entailed_symbols
        if not inferred[p]:
            inferred[p] = True
            entailed_symbols.append(p)
            for c in kb.clauses_with_premise(p):
                count[c] -= 1
                if count[c] == 0:
                    agenda.append(c.args[1])


    return False, None

#This function represents the Backward Chaining (BC) Algorithm
def pl_bc_entails(kb, q, entailed_symbols = None):
    if entailed_symbols == None:
        entailed_symbols = []
    
    if q in entailed_symbols:
        return True, entailed_symbols
    
    for c in kb.clauses_with_conclusion(q):
        all_true = True

        for premise in conjuncts(c.args[0]):
            entailed_symbols.append(premise)

            #Start the caling of the recursive function with the premise
            all_true = all_true and pl_bc_entails(kb, premise, entailed_symbols)
        if all_true:
            entailed_symbols.append(q)
            return True, entailed_symbols
    
    return False, None

# Helper Function
def is_variable(x):
    """A variable is an Expr with no args and a lowercase symbol as the op."""
    return isinstance(x, Expr) and not x.args and x.op[0].islower()