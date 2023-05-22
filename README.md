# Coverings of Riemann Surfaces

Sagemath module for working with (ramified) coverings of Riemann surfaces.

A (ramified) covering of Riemann surfaces is a holomorphic map $f\colon X \to
Y$ between compact Riemann surfaces; hereinafter called just a *covering*.  An
*automorphism* of a covering is an isomorphism $g\colon X \to X$ such that $f =
f\circ g$; the *automorphism group* $\Aut(f)$ is the set of all automorphisms
of $f$ with the composition as operation.  A covering $f\colon X \to Y$ is
*Galois* (or *regular*) if it is equivalent the quotient of $X$ by $\Aut(f)$.

The two main classes defined by this module are `Covering` and
`GaloisCovering`; several methods are defined, which give information about the
coverings, such as the genus, the total ramification or the intermediate
coverings.
