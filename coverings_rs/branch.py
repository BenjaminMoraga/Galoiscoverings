# -*- mode: sage
r"""Sage definition for branch data of coverings of Riemann surfaces

AUTHORS:

- Benjamin Moraga (2023-05-23): initial version
"""

# ****************************************************************************
#    Copyright (C) 2013 Benjamin Moraga <benjamin.baezam@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from functools import cache

from sage.structure.sage_object import SageObject
from sage.groups.perm_gps.permgroup import PermutationGroup_generic
from sage.groups.perm_gps.permgroup_element import PermutationGroupElement
from sage.rings.integer import Integer

from coverings_rs.cover import _check_mon_group


class BranchPoint(SageObject):
    """Brach point of a covering of Riemann surfaces

    For a covering between compact Riemann surfaces `f\colon X \to Y`,
    represent a point `x \in X` such that the multiplicity of `f` in `x`
    is greater than 1.

    EXAMPLES:

    A branch point of multiplicity three::

        sage: A = BranchPoint(3)
        sage: A
        
    """
    
    def __init__(self, mult, check=True):
        """A branch point

        INPUT: ``mult`` -- a positive integer; the multiplicity of
        the branch point

        
        """
        if check:
            if not isinstance(mult, Integer):
                raise TypeError("mult is not an Integer isntance")
            if not mult > 0:
                raise ValueError("mult is not positive")
        self.__mult = mult
            
    def mult(self):
        """Return multiplicity of the branch point"""
        return self.__mult

    def _repr_(self):
        """Return the representation of the branch point"""
        return f"Branch point of multiplicity {self.__mult}"

    def _latex_(self):
        """Return the latex representation of the branch point"""
        return ("\\text{{\\texttt{{Branch value of multiplicity "
                f"{self.__mult}}}}}")

    def __eq__(self, other):
        return isinstance(other, BranchPoint) and self.__mult == other.__mult

    def __hash__(self):
        return hash(self.__mult)
    

class BranchValue(SageObject):
    """Branch value of a covering of Riemann surfaces"""

    def __init__(self, mon_rep, check=True):
        """Branch value of a covering of Riemann surfaces

        Branch value such that a small loop around it has monodromy       
        representation ``mon_rep``.
    
        INPUT:
    
        - ``mon_rep`` -- a permutation

        OUTPUT: a branch value
        """
        if check and not isinstance(mon_rep, PermutationGroupElement):
            raise TypeError("mon_rep is not a permutation")

        self.__rep = mon_rep
        self.__type = mon_rep.cycle_type()

    def type(self):
        """Return the type of the branch value"""
        return self.__type

    @cache
    def mon_rep(self):
        """Return the monodromy representation of the branch value"""
        return self.__rep

    @cache
    def preimages(self):
        """Return the preimages of the branch value"""
        return [BranchPoint(mult) for mult in self.__type]

    @cache
    def deg(self):
        """Return the degree of the branch value"""
        return sum(point.mult()-1 for point in self.preimages())

    def _repr_(self):
        """Represent the branch value"""
        return f"Branch value of type {self.__type}"

    def _latex_(self):
        "Latex representation of the branch value"
        return f"\\text{{\\texttt{{Branch value of type {self.__type}}}}}"

    def __eq__(self, other):
        "Return whether two branch values has the same monodromy"
        return isinstance(other, BranchValue) and self.__rep == other.__rep

    def __hash__(self):
        "Return the hash of the branch value"
        return hash(self.__rep)


def branch_value_types(mon_grp, check=True):
    r"""Return branch values with essentially diferent monodromy

    For a given group monodromy group `G`, return a list with one
    branch value `b_i` for each rational conjugacy class `C_i` of
    `G` such that `b_i` belongs to `C_i`.

    INPUT:

    - ``mon_grp`` -- a transitive permutation group

    - ``check`` -- a boolean (default: ``True``); whether
      ``mon_grp`` is checked as a possible monodromy group or not

    OUTPUT: an interator of BranchValue instances
    """

    if check:
        _check_mon_group(mon_grp)
    return (BranchValue(subgroup.gen())
            for subgroup in mon_grp.conjugacy_classes_subgroups()
            if subgroup.is_cyclic())
