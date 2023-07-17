# -*- mode: sage -*-

from itertools import chain

from sage.misc.cachefunc import cached_method
from sage.structure.parent import Parent
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets

class RationalConjugacyClass(Parent):
    """Rational conjugacy class of an element of a permutation group
    """

    def __init__(self, group, element):
        self._parent = group
        self._representative = element
        Parent.__init__(self, category=FiniteEnumeratedSets())

    def _repr_(self):
        return (f"Rational conjugacy class of {self._representative}"
                f" in {self._parent}")

    def __eq__(self, other):
        if not isinstance(other, RationalConjugacyClass):
            return False
        return self.set() == other.set()

    def __len__(self):
        return len(self.conjugacy_classes())*len(self.conjugacy_classes()[0])

    def __ne__(self, other):
        return not (self == other)

    def __contains__(self, element):
        return element in self.set()

    @cached_method
    def conjugacy_classes(self):
        o = self._representative.order()
        conjugacy_classes = []
        for k in o.coprime_integers(o):
            class_ = self._parent.conjugacy_class(self._representative**k)
            if class_ not in conjugacy_classes:
                conjugacy_classes.append(class_)
        return conjugacy_classes

    @cached_method
    def set(self):
        return DisjointUnionEnumeratedSets(
            [class_.set() for class_ in self.conjugacy_classes()])

    def __iter__(self):
        return iter(self.set())
    
    def list(self):
        return list(self.set())

    def representative(self):
        return self._representative

    an_element = representative


def are_rational_conjugates(group, x, y):
    """Determine if two elements of a group are rational conjugates
    """
    return y in RationalConjugacyClass(group, x)


def rational_conjugacy_classes(group):
    """Return the rational conjugacy classes of a group
    """
    for C in group.conjugacy_classes_subgroups():
        if C.is_cyclic():
            yield RationalConjugacyClass(group, C.gen())


Alter
