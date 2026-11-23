# coxeter-todd-theta-chain
First occurrence in degree four for the Coxeter–Todd theta tower’s 234-eigenline, resolving the Nebe–Teider parameter \(a=0\) and identifying the adjoint return lift.

# First occurrence in the Coxeter–Todd theta tower

In the genus of the rank-12 Coxeter–Todd lattice, there are ten lattice isometry classes. Nebe and Teider narrowed the first nonzero Siegel theta lift of one distinguished eigenline to degree three or four. This manuscript gives an argument for **degree four**, settling their parameter $a=0$.

[Read the manuscript (PDF)](./Coxeter_Todd_Theta_Chain.pdf)

## First occurrence

Let $d_6$ span the eigenline of the Kneser 2-neighbor operator with eigenvalue 234, in Nebe and Teider’s numbering. Theorem 1 gives

$$
\Theta_g(d_6)=0\quad(0\le g\le 3),\qquad F_4=\Theta_4(d_6)\ne 0.
$$

The form $F_4$ is a Siegel cusp form of weight six and level three. In terms of lattice representations, the weighted counts cancel for every Gram matrix of a triple of vectors. At least one Gram matrix of a quadruple has a nonzero weighted count.

## Why degree three is excluded

A hypothetical degree-three lift must reproduce two Hecke eigenvalues at the prime 2. The 2-neighbor eigenvalue 234 fixes the sum of the three reciprocal-coordinate traces at $-23/16$. The maximal-isotropic Hecke eigenvalue 7560 fixes the squared absolute spin trace at $3969/256$. Lemma 3 bounds the modulus of each reciprocal coordinate between $4/9$ and $9/4$. With the sum fixed, Lemma 4 bounds the squared absolute spin trace by $(317/132)^3 < 3969/256$. The two observations are incompatible.

## The return lift

The reverse theta map is the adjoint for the Petersson and lattice mass pairings. Theorem 2 shows that it takes $F_4$ back to $c d_6$, where $c=\lVert F_4\rVert_{\mathrm{Pet}}^2/\lVert d_6\rVert_V^2>0$. Lifting this vector forward in degree three gives zero. Lifting it forward in degree four gives $cF_4$.

## Lean verification

The manuscript describes a Lean formalization of the block restrictions, annulus bound from explicit block data, complex spin identity, rational contradiction, and adjoint argument on a simple eigenline. The first-occurrence theorem in Lean takes the published occurrence table and the passage from a hypothetical cubic lift to local parameter data as hypotheses. The manuscript supplies the lattice identification, automorphic classification input, bounds for general linear groups, and Hecke comparison.

To check the companion source, place `CoxeterToddThetaChain.lean` in a Lean 4.20.0 project with mathlib v4.20.0 and run from the project root:

```sh
lake env lean CoxeterToddThetaChain.lean
```

## Reference

Gabriele Nebe and M. Teider, “Hecke actions on certain strongly modular genera of lattices,” *Archiv der Mathematik* **84** (2005), 46–56. The conjecture follows Theorem 3.4. Page 5 of the manuscript lists the sources for the proof.

## License

Original repository materials are licensed under the [Apache License 2.0](./LICENSE).
