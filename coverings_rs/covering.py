r"""Sage program that works with coverings of Riemann surfaces

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

#__all__ = ['a', 'b', 'c']
__version__ = "0.2"
__author__ = "Benjamin Moraga"

from functools import cache

from sage.structure.sage_object import SageObject

from coverings.branch import BranchPoint, BranchValue

    
class Covering:
    "A class for (ramified) coverings of Riemann surfaces."
    def __init__(self, genus, mon):
        self.__mon = PermutationGroup(mon)
        if not self.__mon.is_transitive():
            raise ValueError("Generated group is not transitive")


class GaloisCovering:
    """
    A class for Galois coverings of Riemann surfaces.
    """
    def __init__(
                self,
                group,
                quotient_genus=None,
                geometric_signature=None
            ):
        self.__aut = group
        self.__quotient_degree = group.order()
        self._intermediate_coverings = {K: None for K
            in group.conjugacy_classes_subgroups()}
        if quotient_genus is None:
            self.__quotient_genus = SR.var('g')
        else:
            self.__quotient_genus = quotient_genus
        if geometric_signature is None:
            geometric_signature = list(
                    SR.var('n', len(ramification_types(group))+1)
                )[1:]
        self.__geometric_signature = dict(zip(ramification_types(group),
                                              geometric_signature))
        self.__signature = {subgroup.order(): sum(
                [num for s, num in self.__geometric_signature.items()
                    if subgroup.order() == s.order()]
            ) for subgroup in self.__geometric_signature}
        self.__quotient_ramification = {mult: num * self.__degree/mult
                               for mult, num
                               in self.__signature.items()}
        self.__total_quotient_ramification = sum(
                [(mult - 1) * num for mult, num
                 in self.__ramification.items()]
            )
        self.__table_of_coverings = [
            [
                i,
                subgroup,
                subgroup.structure_description(),
                group.order()/group.normalizer(subgroup).order(),
                subgroup.order(),
                group.order()/subgroup.order(),
                '*',
                '*',
                '*']
            for i, subgroup in enumerate(self._intermediate_coverings)]

    def intermediate_covering(self, subgroup=None):
        "Return the intermediate covering corresponding to a subgroup"
        if subgroup is None:
            subgroup = self.aut()
        subgroup = self._determine_class(subgroup)
        if self._intermediate_coverings[subgroup] is None:
            self._intermediate_coverings[subgroup] = self if (
                subgroup == self.aut()
            ) else IntermediateCovering(subgroup, parent_covering=self)
            self.__table_of_coverings[
                list(self._intermediate_coverings).index(subgroup)][6:9] = (
                    [self.genus(subgroup)]
                    + list(self.total_ramifications(subgroup)))
        return self._intermediate_coverings[group_class]

    def genus(self, K = None):
        return self._intermediate_covering(K).__quotient_genus

    def GeometricSignature(self, K = None):
        return self._intermediate_covering(K).__geometric_signature

    def Signature(self, K = None):
        return self._intermediate_covering(K).__signature

    def QuotientRamification(self, K = None):
        return self._intermediate_covering.__quotient_ramification

    def InducedRamification(self, K = None, H = None):
        if H is None:
            return self.IntermediateCovering(K)._InducedRamification
        else:
            return self.IntermediateCovering(H).IntermediateCovering(
                self._DetermineClassOfClass(K, H))._InducedRamification

    def InducedRamificationData(self, K = None, H = None):
        if H is None:
            return self.IntermediateCovering(K)._InducedRamificationData
        else:
            return (self.IntermediateCovering(H).IntermediateCovering(
                        self._DetermineClassOfClass(K, H))
                    ._InducedRamificationData)

    def Ramifications(self, K = None, H = None):
        if H is None:
            return (self.QuotientRamification(K),
                    self.InducedRamification(K))
        else:
            return (self.QuotientRamification(K),
                    self.InducedRamification(K,H),
                    self.InducedRamification(H))

    def QuotientTotalRamification(self, K = None):
        return self.IntermediateCovering(K).__QuotientTotalRamification

    def InducedTotalRamification(self, K = None, H = None):
        if H is None:
            return (self.IntermediateCovering(K)
                    ._InducedTotalRamification)
        else:
            return (self.IntermediateCovering(H)
                    .IntermediateCovering(
                        self._DetermineClassOfClass(K, H))
                    ._InducedTotalRamification)

    def TotalRamifications(self, K = None, H = None):
        if H is None:
            return (self.QuotientTotalRamification(K),
                    self.InducedTotalRamification(K))
        else:
            return (self.QuotientTotalRamification(K),
                    self.InducedTotalRamification(K, H),
                    self.InducedTotalRamification(H))

    def intermediate_coverings(self, *show, compute_all=False):
        "Display a table with information about intermediate coverings"
        Header = ['#', '$H$', 'Structure',
                  '$\\left|\\operatorname{Class}(H)\\right|$',
                  '$\\deg \\pi_H $', '$\\deg \\pi^H $', '$g_{X_H}$',
                  '$\\left|R_{\\pi_H}\\right|$',
                  '$\\left|R_{\\pi^H}\\right|$']

        if compute_all is True:
            for code in range(len(self._intermediate_coverings)):
                self.intermediate_covering(code)
        if show != ():
            for code in show:
                self.intermediate_covering(code)
            return table(
                rows = [
                    row for i, row
                    in enumerate(self.__TableOfCoverings)
                    if i in [list(self._IntermediateCoverings)
                             .index(self._DetermineClass(Code))
                             for Code in Show]],
                header_row = Header,
                frame = True)
        return table(rows = self.__TableOfCoverings,
                     header_row = Header,
                     frame = True)

    def InducedIsGalois(self, K, H = None):
        if H is None:
            return self._DetermineClass(K).Size().sage() == 1
        else:
            return self._DetermineClassOfClass(K,H).Size().sage() == 1

    def InducedIsCyclic(self, K, H = None):
        if H is None:
            if self.InducedIsGalois(K):
                return (self._Group().FactorGroup(
                            self._DetermineClass(K).Representative())
                        .IsCyclic().sage())
            else:
                return False
        else:
            if self.InducedIsGalois(K,H):
                return (self.IntermediateCovering(H)._Group()
                        .FactorGroup(self._DetermineClassOfClass(K, H)
                                     .Representative())
                        .IsCyclic().sage())
            else:
                return False

    def InducedAutomorphisms(self, K, H = None):
        if H is None:
            Subgroup = self._DetermineClass(K).Representative()
            return (self._Group().Normalizer(Subgroup)
                    .FactorGroup(Subgroup))
        else:
            Subgroup = (self._DetermineClassOfClass(K, H)
                        .Representative())
            return (self.IntermediateCovering(K)._Group()
                    .Normalizer(Subgroup).FactorGroup(Subgroup))

    def aut(self):
        "Return the group of automorphisms of the covering."
        return self.__aut

    def _determine_class(self, code):
        if code in self._intermediate_coverings:
            return code
        elif isinstance(K, sage.rings.integer.Integer):
            return list(self._intermediate_coverings)[code]
        elif isinstance(K, int):
            return list(self._intermediate_coverings)[code]
        raise ValueError(
                'The argument is not a subgroup of the group of automorphisms'
            )

    def _DetermineClassOfClass(self, K, H):
        GroupH = self.IntermediateCovering(H)._Group()
        for g in self._DetermineClass(K).AsList():
            if GroupH.IsSubgroup(g):
                return self.IntermediateCovering(H)._DetermineClass(g)
        raise Exception('There are no subgroup in the first class '
                        'into a group of the second class')

class IntermediateCovering(GaloisCovering):
    def __init__(self, K, parent_covering):
        if not isinstance(parent_covering, GaloisCovering):
            raise Exception(
                'parent_covering is not a GaloisCovering instance')
        self.__parent_covering = parent_covering
        ParentClass = self.__ParentCovering._DetermineClass(K)
        Subgroup = ParentClass.Representative()
        GeometricSignature = dict(zip(
            ramification_types(Subgroup),
            [0]*len(ramification_types(Subgroup))))
        InducedRamification = {}
        InducedRamificationData = {}
        for StabClass in self.__ParentCovering.GeometricSignature():
            L = [Subgroup.Intersection(Stab)
                 for Stab in StabClass.AsList()]
            RT = []
            for StabClassSub in ramification_types(
                    Subgroup, include_trivial = True):
                Num = L.count(StabClassSub.Representative())
                if Num != 0:
                    Images = (
                        Num * (self.__ParentCovering
                               .GeometricSignature()[StabClass])
                        * (self.__ParentCovering._Group()
                           .Normalizer(StabClass.Representative())
                           .Index(StabClass.Representative()).sage())
                        / (Subgroup.Normalizer(StabClassSub
                                               .Representative())
                           .Index(StabClassSub.Representative())
                           .sage()))
                    if StabClassSub in GeometricSignature:
                        GeometricSignature[StabClassSub] += Images
                    InducedMult = (
                        StabClass.Representative()
                        .IndexNC(StabClassSub.Representative())
                        .sage())
                    RT.append(InducedMult)
                    if InducedMult != 1:
                        if InducedMult in InducedRamification:
                            InducedRamification[InducedMult] += Images
                        else:
                            InducedRamification[InducedMult] = Images
            if RT and not all(R == 1 for R in RT):
                RT.sort(reverse = True)
                RamType = tuple(RT)
                if RamType in InducedRamificationData:
                    InducedRamificationData[RamType] += (
                        self.__ParentCovering
                        .GeometricSignature()[StabClass])
                else:
                    InducedRamificationData[RamType] = (
                        self.__ParentCovering
                        .GeometricSignature()[StabClass])
        InducedDegree = (self.__ParentCovering._Group()
                         .Index(Subgroup).sage())
        InducedTotalRamification = sum(
            [(Mult - 1) * Num for Mult, Num
             in InducedRamification.items()])
        Genus = (
            InducedDegree * (self.__ParentCovering.Genus() - 1) + 1
            + InducedTotalRamification / 2)
        super().__init__(
            Subgroup,
            Genus,
            list(GeometricSignature.values()))
        self._InducedDegree = InducedDegree
        self._InducedRamification = InducedRamification
        self._InducedTotalRamification = InducedTotalRamification
        self._InducedRamificationData = InducedRamificationData
