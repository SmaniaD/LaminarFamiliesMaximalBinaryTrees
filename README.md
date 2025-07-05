# Binary Trees of Pairs of Subsets of a Finite set associated with Laminar Families (Lean 4)

This Lean 4 project formalizes a mathematical structure
**BinaryTreeWithRootandTops**, which models a rooted, ordered
binary tree whose nodes are pairs of disjoint, nonempty, finite
subsets of a finite set `Childs` of “children,” together with a
distinguished set of “tops” acting as the leaves of the tree. 
This is  closely related with laminar families
(https://en.wikipedia.org/wiki/Laminar_set_family ) of subsets
of the set Childs:  Every laminar family of subsets has a rooted 
tree-representation, see Alexander Schrijver. Combinatorial 
Optimization: Polyhedra  and Efficiency, 2004,page 214, Theorem 
13.21.

See the accompanying LaTeX document `manual.tex`, which
provides diagrams and detailed formal notation.

## Features

- Lean 4 definition of `BinaryTreeWithRootandTops`
- Full formalization of its fields:
  - `Childs`: the ground finite set of atoms
  - `Root`: the initial split of `Childs`
  - `Branches`: all pairs that describe the tree
  - `Tops`: the distinguished singleton leaves
- Formal proofs of its structural invariants:
  - nonempty, disjoint pairs
  - the laminar nesting of supports
  - the recursive branching property
- Existence theorem:
  > `exists_tree_childs_eq_C_and_all_childs_in_Tops_of_card_ge_two`
  >
  > Any finite set `Childs` with at least two elements has a 
  > a `BinaryTreeWithRootandTops` whose `Tops` equals the
  > entire  set `Childs` (a maximal tree). This is rooted 
  > tree-representationrelated of  a  maximal
  >  laminar family of subsets of the finite set `Childs`.
  
## One explicit example of maximal BinaryTreeWithRootandTops 

Childs = {1,2,3,4,5,6,7}

Root = ({1,2,3}, {4,5,6,7})

Branches:

({1,2,3},{4,5,6,7})

({1,2},{3})

({4,5},{6,7})

({1},{2})

({4},{5})

({6},{7})

Tops = {1,2,3,4,5,6,7}

Its tree structure is:
                                  {1,2,3,4,5,6,7} Childs
                                          |
                                ({1,2,3}, {4,5,6,7}) root <- branch
                               /                       \
                    ({1,2}, {3}) <-branch            ({4,5}, {6,7}) <-branch
                      /         \                    /           \
    branch->({1}, {2})           3        branch->({4}, {5})   ({6}, {7}) <-branch
              /     \          (top)              /       \     /       \
           1(top)  2(top)                   4(top)    5(top) 6(top)   7(top)

 This  is a rooted tree-representationrelated  a  maximal laminar family
 {1,2,3,4,5,6,7}, {1,2,3}, {4,5,6,7}, {1,2}, {4,5}, {6,7}, {1},{2},{3},{4},{5},{6},{7}
