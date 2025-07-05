# Binary Trees of Subsets of a Finite set associated with Laminar Families (Lean 4)

This Lean 4 project formalizes a mathematical structure
**BinaryTreeWithRootandTops**, which models a rooted, ordered
binary tree whose nodes are pairs of disjoint, nonempty, finite
subsets of a finite Childs set of “children,” together with a
distinguished set of “tops” acting as the leaves of the tree. 
This is  closely related with laminar families of subsets of Childs.

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
  > Any Childs set of at least two elements can be turned into
  > a `BinaryTreeWithRootandTops` whose `Tops` equals the
  > entire ground set. This is related to the existence of maximal
  >  laminar families of subsets of the finite set Childs. 
-  One explicit example of BinaryTreeWithRootandTops is 

Childs = {1,2,3,4,5,6,7}

Root = ({1,2,3}, {4,5,6,7})

Branches including:

({1,2,3},{4,5,6,7})

({1,2},{3})

({4,5},{6,7})

({1},{2})

({4},{5})

({6},{7})

Tops = {1,2,3,4,5,6,7}

Its tree structure is:

                                ({1,2,3}, {4,5,6,7}) root 
                               /                       \
                    ({1,2}, {3})                  ({4,5}, {6,7})
                      /         \                    /           \
            ({1}, {2})           3                ({4}, {5})   ({6}, {7})
              /     \          (top)              /       \     /       \
           1(top)  2(top)                   4(top)    5(top) 6(top)   7(top)
