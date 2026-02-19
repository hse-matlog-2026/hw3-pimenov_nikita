# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        p = Formula('p')
        if formula.root == 'T':
            return Formula('|', p, Formula('~', p))
        return Formula('&', p, Formula('~', p))
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    first = to_not_and_or(formula.first)
    second = to_not_and_or(formula.second)
    if formula.root == '&':
        return Formula('&', first, second)
    if formula.root == '|':
        return Formula('|', first, second)
    if formula.root == '->':
        return Formula('|', Formula('~', first), second)
    if formula.root == '+':
        return Formula('|',
                       Formula('&', first, Formula('~', second)),
                       Formula('&', Formula('~', first), second))
    if formula.root == '<->':
        return Formula('|',
                       Formula('&', first, second),
                       Formula('&', Formula('~', first), Formula('~', second)))
    if formula.root == '-&':
        return Formula('~', Formula('&', first, second))
    if formula.root == '-|':
        return Formula('~', Formula('|', first, second))
    raise ValueError('Unknown operator: ' + formula.root)

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        p = Formula('p')
        contradiction = Formula('&', p, Formula('~', p))
        if formula.root == 'F':
            return contradiction
        return Formula('~', contradiction)
    if is_unary(formula.root):
        return Formula('~', to_not_and(formula.first))
    first = to_not_and(formula.first)
    second = to_not_and(formula.second)
    if formula.root == '&':
        return Formula('&', first, second)
    if formula.root == '|':
        return Formula('~', Formula('&', Formula('~', first), Formula('~', second)))
    if formula.root == '->':
        return Formula('~', Formula('&', first, Formula('~', second)))
    if formula.root == '+':
        left = Formula('&', first, Formula('~', second))
        right = Formula('&', Formula('~', first), second)
        return Formula('~', Formula('&', Formula('~', left), Formula('~', right)))
    if formula.root == '<->':
        xor = to_not_and(Formula('+', formula.first, formula.second))
        return Formula('~', xor)
    if formula.root == '-&':
        return Formula('~', Formula('&', first, second))
    if formula.root == '-|':
        return Formula('&', Formula('~', first), Formula('~', second))
    raise ValueError('Unknown operator: ' + formula.root)

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    not_and = to_not_and(formula)
    def convert(f: Formula) -> Formula:
        if is_variable(f.root):
            return f
        if is_unary(f.root):
            inner = convert(f.first)
            return Formula('-&', inner, inner)
        first = convert(f.first)
        second = convert(f.second)
        nand = Formula('-&', first, second)
        return Formula('-&', nand, nand)
    return convert(not_and)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    def imp(a: Formula, b: Formula) -> Formula:
        return Formula('->', a, b)
    def neg(a: Formula) -> Formula:
        return Formula('~', a)
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        p = Formula('p')
        t = imp(p, p)
        if formula.root == 'T':
            return t
        return neg(t)
    if is_unary(formula.root):
        return neg(to_implies_not(formula.first))
    first = to_implies_not(formula.first)
    second = to_implies_not(formula.second)
    if formula.root == '->':
        return imp(first, second)
    if formula.root == '|':
        return imp(neg(first), second)
    if formula.root == '&':
        return neg(imp(first, neg(second)))
    if formula.root == '+':
        return imp(imp(first, second), neg(imp(second, first)))
    if formula.root == '<->':
        return neg(imp(imp(first, second), neg(imp(second, first))))
    if formula.root == '-&':
        return imp(first, neg(second))
    if formula.root == '-|':
        return neg(imp(neg(first), second))
    raise ValueError('Unknown operator: ' + formula.root)

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    implies_not = to_implies_not(formula)
    def eliminate(f: Formula) -> Formula:
        if is_variable(f.root):
            return f
        if is_unary(f.root):
            return Formula('->', eliminate(f.first), Formula('F'))
        return Formula('->', eliminate(f.first), eliminate(f.second))
    return eliminate(implies_not)
