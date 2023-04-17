
def RamificationTypes(Group, IncludeTrivial = False):
    if isinstance(Group, sage.libs.gap.element.GapElement): 
        G = Group 
    else:
        G = Group.gap()
    if IncludeTrivial:
        return [G.ConjugacyClassSubgroups(G.Subgroup(
                    [H.Representative()]))
                for H in list(G.RationalClasses())]
    else:    
        return [G.ConjugacyClassSubgroups(G.Subgroup(
                    [H.Representative()]))
                for H in list(G.RationalClasses())[1:]]

class GaloisCovering:
    def __init__(
            self, Group, QuotientGenus = None,
            GeometricSignature = None):
        if isinstance(Group, sage.libs.gap.element.GapElement): 
            self.__Group = Group
        else: 
            self.__Group = Group.gap()
        self.__QuotientDegree = self.__Group.Order().sage()
        if self._Group().Order().sage() != 1:
            self._IntermediateCoverings = {K : None for K in list(
                self.__Group.ConjugacyClassesSubgroups())} 
        else: 
            self._IntermediateCoverings = {self._Group(
                ).ConjugacyClassSubgroups(self._Group()) : self}
        if QuotientGenus is None:
            self.__QuotientGenus = var('g')
        else:
            self.__QuotientGenus = QuotientGenus
        if GeometricSignature is None:
            if self.__Group.Order().sage() != 1:
                GeometricSignature = list(var(
                    ['n' + str(j + 1) for j 
                     in range(len(RamificationTypes(self.__Group)))]))
            else: 
                GeometricSignature = []
        self.__GeometricSignature = dict(zip(RamificationTypes(
            self.__Group), GeometricSignature))
        self.__Signature = {StabClass.Representative().Order().sage() 
                            : sum([Num for S, Num 
                                   in self.__GeometricSignature.items() 
                                   if (StabClass
                                       .Representative()
                                       .Order()
                                       .sage()) == (S.Representative()
                                                    .Order()
                                                    .sage())]) 
                            for StabClass in self.__GeometricSignature}
        self.__QuotientRamification = {
            Mult : Num * self.__QuotientDegree/Mult 
            for Mult, Num in self.__Signature.items()}
        self.__QuotientTotalRamification = sum(
            [(Mult- 1) * Num for Mult, Num 
             in self.__QuotientRamification.items()])
        self._InducedDegree = 1
        self._InducedRamification = {}
        self._InducedRamificationData = {}
        self._InducedTotalRamification = 0
        self.__TableOfCoverings = [
            [
                i,
                PermutationGroup(list(
                    Class.Representative().GeneratorsOfGroup())),
                PermutationGroup(list(
                    Class.Representative().GeneratorsOfGroup()))
                    .structure_description(),
                Class.Size(),
                Class.Representative().Order().sage(),
                self._Group().Index(Class.Representative()).sage(),
                '*',
                '*',
                '*'] 
            for i, Class in enumerate(self._IntermediateCoverings)]
    
    def IntermediateCovering(self, K = None):
        if K is None:
            K = self._Group()
        Class = self._DetermineClass(K)
        if self._IntermediateCoverings[Class] == None:
            self._IntermediateCoverings[Class] = self if Class == list(
                self._IntermediateCoverings)[-1] else (
                    IntermediateCovering(Class, ParentCovering = self))
            self.__TableOfCoverings[
                list(self._IntermediateCoverings).index(Class)][6:9] = (
                    [self.Genus(Class)] 
                    + list(self.TotalRamifications(Class)))
        return self._IntermediateCoverings[Class]
    
    def Genus(self, K = None):
        return self.IntermediateCovering(K).__QuotientGenus
    
    def GeometricSignature(self, K = None):
        return self.IntermediateCovering(K).__GeometricSignature
    
    def Signature(self, K = None):
        return self.IntermediateCovering(K).__Signature
    
    def QuotientRamification(self, K = None):
        return self.IntermediateCovering(K).__QuotientRamification
    
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

    def IntermediateCoverings(self, *Show, ComputeAll = False):
        Header = ['#', '$H$', 'Structure', 
                  '$\\left|\\operatorname{Class}(H)\\right|$',
                  '$\\deg \\pi_H $', '$\\deg \\pi^H $', '$g_{X_H}$',
                  '$\\left|R_{\\pi_H}\\right|$', 
                  '$\\left|R_{\\pi^H}\\right|$']
        if Show is not ():
            for Code in Show:
                self.IntermediateCovering(Code)
            return table(
                rows = [
                    row for i, row 
                    in enumerate(self.__TableOfCoverings) 
                    if i in [list(self._IntermediateCoverings)
                             .index(self._DetermineClass(Code)) 
                             for Code in Show]],
                header_row = Header,
                frame = True)
        if ComputeAll is True:
            for Code in range(len(self._IntermediateCoverings)):
                self.IntermediateCovering(Code)
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
        
    def _Group(self):
        return self.__Group
            
    def _DetermineClass(self, K):
        if K in self._IntermediateCoverings:
            return K
        elif isinstance(K, sage.rings.integer.Integer):
            return list(self._IntermediateCoverings.keys())[K]
        elif isinstance(K, int):
            return list(self._IntermediateCoverings.keys())[K]
        else:
            try:
                ClassK = (
                    self.__Group.ConjugacyClassSubgroups(
                        self.__Group.AsSubgroup(K)) 
                    if isinstance(K, sage.libs.gap.element.GapElement) 
                    else self.__Group.ConjugacyClassSubgroups(
                        self.__Group.AsSubgroup(K.gap())))
            except:
                raise Exception(
                    'The argument is not a subgroup of self.__Group')
            for ClassH in self._IntermediateCoverings:
                if ClassK == ClassH:
                    return ClassH
        
    def _DetermineClassOfClass(self, K, H):
        GroupH = self.IntermediateCovering(H)._Group()
        for g in self._DetermineClass(K).AsList():
            if GroupH.IsSubgroup(g):
                return self.IntermediateCovering(H)._DetermineClass(g)
        raise Exception('There are no subgroup in the first class '
                        'into a group of the second class')
            
class IntermediateCovering(GaloisCovering):
    def __init__(self, K, ParentCovering):
        if not isinstance(ParentCovering, GaloisCovering):
            raise Exception(
                'SuperCovering is not a GaloisCovering instance')
        self.__ParentCovering = ParentCovering
        ParentClass = self.__ParentCovering._DetermineClass(K)
        Subgroup = ParentClass.Representative()
        GeometricSignature = dict(zip(
            RamificationTypes(Subgroup), 
            [0]*len(RamificationTypes(Subgroup))))
        InducedRamification = {}
        InducedRamificationData = {}
        for StabClass in self.__ParentCovering.GeometricSignature():
            L = [Subgroup.Intersection(Stab) 
                 for Stab in StabClass.AsList()]
            RT = []
            for StabClassSub in RamificationTypes(
                    Subgroup, IncludeTrivial = True):
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
