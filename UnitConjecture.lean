import UnitConjecture.GardamTheorem

/-!
# Formalization: Gardam's disproof of the Kaplansky Unit Conjecture

This library contains the formalization of the [disproof](https://arxiv.org/abs/2102.11818) of the Kaplansky Unit Conjecture by Giles Gardam in a paper in the Annals of Mathematics.
Here is an outline of the code:
![](UnitConjecture/depgraph.dot.svg)

## The Proof

Gardam proved that for a group `P` (the *Promislow* or *Hantzsche–Wendt* group), we have the following:

* `P` is torsion free; this is proved in [`TorsionFree.lean`](UnitConjecture/TorsionFree.html)
* `P` has non-trivial units; this is proved in [`GardamTheorem.lean`](UnitConjecture/GardamTheorem.html)

The rest of the code is required to construct $P$, construct group rings, and to prove the required properties.

## Constructing the group `P`

The group `P` is a so called _Metabelian Group_, an extension of an abelian group by an abelian group. 

* In the file [`GardamGroup.lean`](UnitConjecture/GardamGroup.html), the specific construction of `P` is given using the general construction of Metabelian groups.
* In the file [`MetabelianGroup.lean`](UnitConjecture/MetabelianGroup.html), Metabelian Groups are constructed based on appropriate data, and proved to be groups.
* The data for a Metabelian group includes a _group action_ and a _cocycle_. These are defined and their basic properties proved in [`Cocycle.lean`](UnitConjecture/Cocycle.html).

## Constructing group rings

A group ring $K[G]$ is the free module on $K$ with basis elements of a group $G$ with a natural ring structure.

* Free modules are constructed in [`FreeModule.lean`](UnitConjecture/FreeModule.html) with properties proved. This crucially includes decidable equality of elements, assuming decidable equality for $G$ and $R$.
* The Group Ring structure is defined in [`GroupRing.lean`](UnitConjecture/GroupRing.html) and shown to give a ring.

## Proofs and Definitions by Computation and Enumeration

We set things up to use typeclasses to deduce decidable equality, both by finite enumeration and by checking equality on a basis for finitely generated abelian groups.

* In [`EnumDecide.lean`](UnitConjecture/EnumDecide.html) we set up the typeclasses for deducing decidable equality, and prove the basic cases.
* In [`AddFreeGroup.lean`](UnitConjecture/AddFreeGroup.html) we define bases of free abelian groups via a universal property, show that products of $\mathbb{Z}$ have bases, show that homormorphisms can be defined by giving functions on a basis, and show that we have decidable equality for homomorphisms on finitely generated free abelian groups.
-/
