# Formalization: Gardam's disproof of the Kaplansky Unit Conjecture

This folder contains the formalization of the disproof of the Kaplansky Unit Conjecture by [Gardam](https://arxiv.org/abs/2102.11818) in a paper in the Annals of Mathematics.
Here is an outline of the code:

## The Proof

Gardam proved that for a group $P$ (the *Promislow* or *Hantzsche–Wendt* group), we have the following:

* $P$ is torsion free -- proved in `TorsionFree.lean`
* $P$ has non-trivial units -- proved in `UnitConjecture.lean`

The rest of the code is required to construct $P$, construct group rings, and to prove the required properties.

## Constructing the group `P`

The group `P` is a _Metabelian Group_. 

* In the file `GardamGroup.lean`, the specific construction of `P` is given using the general construction of Metabelian groups.
* In the file `MetabelianGroup.lean`, _Metabelian Groups_ are constructed based on appropriate data, and proved to be groups.
* The data for a Metabelian group includes a _Group Action_. These are defined and their basic properties proved in `GroupAction.lean`.
* Product groups are defined, as a special case, in `ProductGroups.lean`.
* Homomorphisms are defined in `Morphisms.lean` and some properties are proved.

## Constructing group rings

A group ring $K[G]$ is a ring structure on the free module on $K$ with basis elements of a group $G$.

* Free modules are constructed in `FreeModule.lean` with properties proved. This crucially includes decidable equality of elements, assuming decidable equality for $G$ and $R$.
* The Group Ring structure is defined in `GroupRing.lean` and shown to give a ring.

## Proofs and Definitions by Computation and Enumeration

We set things up to use typeclasses to deduce decidable equality, both by finite enumeration and by checking equality on a basis for finitely generated abelian groups.

* In `EnumDecide.lean` we set up the typeclasses for deducing decidable equality, and prove the basic cases.
* In `FreeAbelianGroup.lean` we define bases of free abelian groups via a universal property, show that products of $\mathbb{Z}$ have bases, and show that we have decidable equality for homomorphisms on finitely generated free abelian groups.




