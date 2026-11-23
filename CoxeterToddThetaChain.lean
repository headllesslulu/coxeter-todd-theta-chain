import Mathlib.Data.Complex.Norm
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The Coxeter–Todd theta tower: exclusion in degree three

Lean 4.20.0, mathlib v4.20.0. Run `lake env lean CoxeterToddThetaChain.lean`.

The concrete core is `no_degree_three_parameters`. It quantifies over ordinary
complex numbers. No automorphic facts are postulated as axioms. The last
theorems have explicit inputs for the results of Nebe–Teider, the unramified
theta correspondence, and the automorphic bounds used in the companion proof.
-/

namespace CoxeterToddThetaChain

/-- Standard trace contribution of one reciprocal pair. -/
noncomputable def pairTrace (z : ℂ) : ℝ := (z + z⁻¹).re

/-- Squared absolute spin-character contribution of one reciprocal pair. -/
noncomputable def spinFactor (z : ℂ) : ℝ := ‖2 + z + z⁻¹‖

def weightSix (w : ℤ) : Prop :=
  w = -5 ∨ w = -4 ∨ w = -3 ∨ w = 0 ∨ w = 3 ∨ w = 4 ∨ w = 5

/-- No four consecutive weights occur in the degree-three, weight-six standard parameter. -/
theorem no_four_consecutive (w : ℤ) :
    ¬ (weightSix w ∧ weightSix (w+1) ∧ weightSix (w+2) ∧ weightSix (w+3)) := by
  unfold weightSix
  omega

/-- A string whose weights occur in the infinitesimal character has length at most three. -/
theorem string_length_bound {d : ℕ} (w : ℤ)
    (weights : ∀ j : ℕ, j < d → weightSix (w + j)) : d ≤ 3 := by
  by_contra! h
  exact no_four_consecutive w
    ⟨by simpa using weights 0 (by omega), weights 1 (by omega),
     weights 2 (by omega), weights 3 (by omega)⟩

theorem no_character_triple : ¬ weightSix 1 := by norm_num [weightSix]

/-- A length-three Arthur string must come from GL₂ once GL₁ has been excluded. -/
theorem rank_of_triple {m : ℕ} (hm : 0 < m) (hdim : 3 * m ≤ 7) (hchar : m ≠ 1) :
    m = 2 := by omega

/-- Eighth-power version of the weakened GL₂ bound at 2, including the largest
Arthur shift in a string of length three. -/
theorem shifted_gl_two_bound {r : ℝ} (hr : r ^ 8 ≤ 2) : 2 * r ≤ 9 / 4 := by
  by_contra! h
  have ht : (9/8 : ℝ) < r := by linarith
  have hu : (9/8 : ℝ) ^ 8 < r ^ 8 := pow_lt_pow_left₀ ht (by norm_num) (by decide)
  norm_num at hu
  linarith

/-- A GL exponent of at most one half and an Arthur shift of at most one half. -/
theorem short_string_bound {r s : ℝ} (hr : r ^ 2 ≤ 2) (hs : s ^ 2 ≤ 2) :
    r * s ≤ 2 := by nlinarith [sq_nonneg (r - s)]

/-- Data of one standard eigenvalue from an Arthur block. The two bounds on the
unshifted GL parameter are the Jacquet–Shalika and GL₂ bounds. The shift bounds
are the largest weights in strings of lengths at most two and three. -/
structure ArthurEntry (radius : ℝ) where
  rank : ℕ
  length : ℕ
  rank_pos : 0 < rank
  dimension : length * rank ≤ 7
  start : ℤ
  weights : ∀ j : ℕ, j < length → weightSix (start + j)
  character_center : rank = 1 → 2 * start + (length : ℤ) - 1 = 0
  base : ℝ
  shift : ℝ
  base_nonneg : 0 ≤ base
  scaled : radius = base * shift
  gl_bound : base ^ 2 ≤ 2
  gl_two_bound : rank = 2 → base ^ 8 ≤ 2
  short_shift : length ≤ 2 → shift ^ 2 ≤ 2
  triple_shift : length = 3 → shift ≤ 2

theorem ArthurEntry.radius_bound {r : ℝ} (e : ArthurEntry r) : r ≤ 9/4 := by
  have hd := string_length_bound e.start e.weights
  by_cases h : e.length ≤ 2
  · rw [e.scaled]
    have hh := short_string_bound e.gl_bound (e.short_shift h)
    linarith
  · have h3 : e.length = 3 := by omega
    have hm : e.rank ≠ 1 := by
      intro h1
      have hcenter := e.character_center h1
      rw [h3] at hcenter
      have hstart : e.start = -1 := by omega
      have hw := e.weights 2 (by omega)
      rw [hstart] at hw
      exact no_character_triple (by norm_num at hw ⊢; exact hw)
    have hdim : 3 * e.rank ≤ 7 := by simpa [h3] using e.dimension
    have h2 := rank_of_triple e.rank_pos hdim hm
    have hb := shifted_gl_two_bound (e.gl_two_bound h2)
    rw [e.scaled]
    nlinarith [mul_nonneg e.base_nonneg (sub_nonneg.mpr (e.triple_shift h3))]

def ArthurPair (z : ℂ) : Prop :=
  z ≠ 0 ∧ Nonempty (ArthurEntry ‖z‖) ∧ Nonempty (ArthurEntry ‖z⁻¹‖)

theorem annulus_of_arthur_pair {z : ℂ} (h : ArthurPair z) :
    (4/9 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 9/4 := by
  obtain ⟨hn, ⟨e⟩, ⟨f⟩⟩ := h
  have hf := f.radius_bound
  rw [norm_inv, ← one_div] at hf
  have hh := (div_le_iff₀ (norm_pos_iff.mpr hn)).mp hf
  exact ⟨by linarith, e.radius_bound⟩

/-- Extract the degree-three pair trace from the Kneser eigenvalue. -/
theorem trace_calibration {u : ℝ}
    (h : 32 * (1 + u + (4 + 2 + 1 + 1/2 + 1/4)) = 234) :
    u = -23 / 16 := by linarith

/-- The degree-three adjacency formula of Walling and the Rallis standard-trace
formula give identical values for every pair trace sum. -/
theorem two_standard_normalizations (u : ℝ) :
    4 * (8*u + 7) + 252 = 32 * (1+u + (4+2+1+1/2+1/4)) := by ring

theorem degree_four_adjacency {t : ℝ} (h : 2*t + 114 = 234) : t = 60 := by linarith

/-- Ratio of the two mass-normalized spin traces, using the trivial eigenline. -/
theorem spin_calibration :
    ((7560 : ℝ) / 151470 * ((1 + 8) * (1 + 16) * (1 + 32) / 64)) ^ 2
      = 3969 / 256 := by norm_num

theorem complex_factor_formula {z : ℂ} (hz : z ≠ 0) :
    spinFactor z = (‖z‖ + 1 / ‖z‖) + 2 * (z.re / ‖z‖) ∧
    pairTrace z = (‖z‖ + 1 / ‖z‖) * (z.re / ‖z‖) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have he : 2 + z + z⁻¹ = (z + 1)^2 / z := by
    field_simp
    ring
  have hadd : ‖z+1‖ ^ 2 = ‖z‖ ^ 2 + 1 + 2*z.re := by
    rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_eq_norm_sq z]
    simp
  constructor
  · rw [spinFactor, he, norm_div, norm_pow, hadd]
    field_simp
    ring
  · rw [pairTrace, Complex.add_re, Complex.inv_re, Complex.normSq_eq_norm_sq]
    field_simp
    ring

theorem factor_times_radius {z : ℂ} (hz : z ≠ 0) :
    spinFactor z * ‖z‖ = ‖1 + z‖ ^ 2 := by
  have he : 2 + z + z⁻¹ = (1+z)^2 / z := by
    field_simp
    ring
  rw [spinFactor, he, norm_div, norm_pow, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

/-- The unitary central-character relation turns the squared spin trace into
a product depending only on the three coordinates of the standard parameter. -/
theorem squared_spin_trace (a x y z : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (central : ‖a‖ ^ 2 * ‖x‖ * ‖y‖ * ‖z‖ = 1) :
    ‖a * (1+x) * (1+y) * (1+z)‖ ^ 2 = spinFactor x * spinFactor y * spinFactor z := by
  simp only [norm_mul, mul_pow]
  rw [← factor_times_radius hx, ← factor_times_radius hy, ← factor_times_radius hz]
  calc
    _ = (‖a‖^2 * ‖x‖ * ‖y‖ * ‖z‖) *
        (spinFactor x * spinFactor y * spinFactor z) := by ring
    _ = _ := by rw [central, one_mul]

/-- The annulus estimate on one factor is affine in the *same* pair's real trace. -/
theorem factor_le_trace {z : ℂ} (lo : (4/9 : ℝ) ≤ ‖z‖) (hi : ‖z‖ ≤ 9/4) :
    spinFactor z ≤ 11/4 + (8/11) * pairTrace z := by
  have hp : 0 < ‖z‖ := by linarith
  have hz := norm_pos_iff.mp hp
  obtain ⟨hspin, htrace⟩ := complex_factor_formula hz
  let A := ‖z‖ + 1 / ‖z‖
  let c := z.re / ‖z‖
  have hA : A ≤ 11 / 4 := by
    have hh : ‖z‖ ^ 2 + 1 ≤ (97/36) * ‖z‖ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi)]
    have hdiv := (div_le_iff₀ hp).mpr hh
    have hi' : A = (‖z‖ ^ 2 + 1) / ‖z‖ := by
      dsimp [A]
      field_simp
      ring
    rw [hi']
    linarith
  have hc : c ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using Complex.re_le_norm z)
  have hprod := mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ 11/4 - 2*c by linarith)
  change spinFactor z = A + 2*c at hspin
  change pairTrace z = A*c at htrace
  rw [hspin, htrace]
  nlinarith

private theorem amgm_at_min {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c) :
    27*a*b*c ≤ (a+b+c)^3 := by
  let x := b-a
  let y := c-a
  have hx : 0 ≤ x := sub_nonneg.mpr hab
  have hy : 0 ≤ y := sub_nonneg.mpr hac
  have hq : 0 ≤ x^2 - x*y + y^2 := by
    nlinarith [sq_nonneg (x-y), sq_nonneg x, sq_nonneg y]
  have hp := mul_nonneg ha hq
  have hc : 0 ≤ (x+y)^3 := pow_nonneg (add_nonneg hx hy) _
  have hid : (a+b+c)^3 - 27*a*b*c =
      9*a*(x^2-x*y+y^2) + (x+y)^3 := by dsimp [x, y]; ring
  linarith

private theorem amgm_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27*a*b*c ≤ (a+b+c)^3 := by
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · exact amgm_at_min ha hab hac
    · nlinarith only [amgm_at_min hc hca (hca.trans hab)]
  · rcases le_total b c with hbc | hcb
    · nlinarith only [amgm_at_min hb hba hbc]
    · nlinarith only [amgm_at_min hc (hcb.trans hba) hcb]

/-- Exact trace-constrained upper bound on the product over a complex triple. -/
theorem spin_product_bound (x y z : ℂ)
    (hx : (4/9 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 9/4)
    (hy : (4/9 : ℝ) ≤ ‖y‖ ∧ ‖y‖ ≤ 9/4)
    (hz : (4/9 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 9/4)
    (htrace : pairTrace x + pairTrace y + pairTrace z = -23/16) :
    spinFactor x * spinFactor y * spinFactor z ≤ (317/132 : ℝ)^3 := by
  have hsum : spinFactor x + spinFactor y + spinFactor z ≤ 317/44 := by
    linarith [factor_le_trace hx.1 hx.2, factor_le_trace hy.1 hy.2,
      factor_le_trace hz.1 hz.2]
  have hn (w : ℂ) : 0 ≤ spinFactor w := norm_nonneg _
  have hcube := pow_le_pow_left₀ (add_nonneg (add_nonneg (hn x) (hn y)) (hn z)) hsum 3
  linarith only [hcube, amgm_three (hn x) (hn y) (hn z)]

/-- There is no candidate Satake triple with the two published eigenvalues
and the unconditional automorphic annulus. -/
theorem no_degree_three_parameters (x y z : ℂ)
    (hx : (4/9 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 9/4)
    (hy : (4/9 : ℝ) ≤ ‖y‖ ∧ ‖y‖ ≤ 9/4)
    (hz : (4/9 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 9/4)
    (htrace : pairTrace x + pairTrace y + pairTrace z = -23/16)
    (hspin : spinFactor x * spinFactor y * spinFactor z = 3969/256) : False := by
  have h := spin_product_bound x y z hx hy hz htrace
  rw [hspin] at h
  norm_num at h

/-- The published lattice eigenvalues, the two unramified transfer formulas,
and the standard Arthur blocks at 2 for a hypothetical degree-three cusp form. -/
def CompatibleAtTwo (a x y z : ℂ) : Prop :=
  ArthurPair x ∧ ArthurPair y ∧ ArthurPair z ∧
  32 * (1 + (pairTrace x + pairTrace y + pairTrace z) + (4+2+1+1/2+1/4)) = 234 ∧
  ‖a‖ ^ 2 * ‖x‖ * ‖y‖ * ‖z‖ = 1 ∧
  ((1+1)*(1+2)*(1+4) : ℝ) * 64 * ‖a * (1+x) * (1+y) * (1+z)‖ = 7560

theorem incompatible_published_data (a x y z : ℂ) (h : CompatibleAtTwo a x y z) : False := by
  obtain ⟨hx, hy, hz, htrace, central, hspin⟩ := h
  have habs : ‖a*(1+x)*(1+y)*(1+z)‖ = 63/16 := by linarith
  have hp := squared_spin_trace a x y z hx.1 hy.1 hz.1 central
  rw [habs] at hp
  exact no_degree_three_parameters x y z (annulus_of_arthur_pair hx)
    (annulus_of_arthur_pair hy) (annulus_of_arthur_pair hz) (trace_calibration htrace)
    (by linarith only [hp])

/-- The source table leaves 3 or 4 as the first occurrence. A lift in degree 3
would supply these spherical and Arthur data by the comparison theorems. -/
theorem first_occurrence_four (occurs : ℕ → Prop)
    (table : (∀ n < 3, ¬ occurs n) ∧ occurs 4)
    (comparison : occurs 3 → ∃ a x y z : ℂ, CompatibleAtTwo a x y z) :
    (∀ n < 4, ¬ occurs n) ∧ occurs 4 := by
  refine ⟨?_, table.2⟩
  intro n hn
  rcases Nat.lt_or_eq_of_le (show n ≤ 3 by omega) with hlt | rfl
  · exact table.1 n hlt
  · intro h
    obtain ⟨a, x, y, z, hs⟩ := comparison h
    exact incompatible_published_data a x y z hs

abbrev Gram (g : ℕ) := Matrix (Fin g) (Fin g) ℤ
abbrev TupleMatrix (g : ℕ) := Matrix (Fin 12) (Fin g) ℤ

/-- The integral Fourier index of a tuple. Even positive definite lattices have
finite representation fibers, including for singular indices. -/
def Representations {g : ℕ} (B : Gram 12) (T : Gram g) :=
  {X : TupleMatrix g // X.transpose * B * X = T}

structure LatticeGram where
  matrix : Gram 12
  finite_fibers : ∀ g (T : Gram g), Finite (Representations matrix T)

noncomputable def representationCount (L : LatticeGram) {g : ℕ} (T : Gram g) : ℕ :=
  Nat.card (Representations L.matrix T)

noncomputable def thetaCoefficient (lattices : Fin 10 → LatticeGram) (d : Fin 10 → ℂ)
    {g : ℕ} (T : Gram g) : ℂ :=
  ∑ i, d i * (representationCount (lattices i) T : ℂ)

def thetaOccurs (lattices : Fin 10 → LatticeGram) (d : Fin 10 → ℂ) (g : ℕ) : Prop :=
  ∃ T : Gram g, thetaCoefficient lattices d T ≠ 0

/-- Fourier-coefficient statement for ten rank-twelve lattices. In the
Coxeter–Todd genus the occurrence table is furnished by Nebe–Teider and the
implication `local_data` is proved by the automorphic comparison in the paper. -/
theorem first_occurrence_for_theta_coefficients (lattices : Fin 10 → LatticeGram)
    (d : Fin 10 → ℂ)
    (table : (∀ n < 3, ¬ thetaOccurs lattices d n) ∧ thetaOccurs lattices d 4)
    (local_data : thetaOccurs lattices d 3 → ∃ a x y z : ℂ, CompatibleAtTwo a x y z) :
    (∀ n < 4, ∀ T : Gram n, thetaCoefficient lattices d T = 0) ∧
      ∃ T : Gram 4, thetaCoefficient lattices d T ≠ 0 := by
  obtain ⟨hv, hn⟩ := first_occurrence_four (thetaOccurs lattices d) table local_data
  refine ⟨?_, hn⟩
  intro n hlt T
  by_contra h
  exact hv n hlt ⟨T, h⟩

/-- Adjoint Hecke equivariance against a fixed cusp eigenform, allowing the
first input of the Petersson pairing to have an Eisenstein part. -/
theorem reverse_lift_is_eigenvector {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (K : V →ₗ[ℂ] V) (H : W →ₗ[ℂ] W)
    (up : V →ₗ[ℂ] W) (f : W) (back : V) (ev : ℂ)
    (mass : V → V → ℂ) (pet : W → W → ℂ)
    (separates : ∀ v w, (∀ t, mass t v = mass t w) → v = w)
    (adjoint : ∀ t, mass t back = pet (up t) f)
    (kSelf : ∀ t, mass t (K back) = mass (K t) back)
    (hSelf : ∀ t, pet (H (up t)) f = pet (up t) (H f))
    (mass_scale : ∀ t, mass t (ev • back) = (star ev) * mass t back)
    (pet_scale : ∀ t, pet (up t) (ev • f) = (star ev) * pet (up t) f)
    (forward : ∀ t, up (K t) = H (up t)) (eigen : H f = ev • f) :
    K back = ev • back := by
  apply separates
  intro t
  rw [kSelf, adjoint, forward, hSelf, eigen, pet_scale, mass_scale, adjoint]

/-- In the mass pairing, a strictly positive squared norm forces a nonzero return.
The pairing is given only against the fixed cusp form, so this statement does
not require every theta series to have finite Petersson norm. -/
theorem nonzero_return_of_pairing {V : Type*} [Zero V] (pair : V → V → ℂ)
    (pair_zero : ∀ v, pair v 0 = 0) (d back : V) (normSquared : ℝ)
    (hpos : 0 < normSquared) (adjoint : pair d back = (normSquared : ℂ)) :
    back ≠ 0 := by
  intro h
  rw [h, pair_zero] at adjoint
  have hr := congrArg Complex.re adjoint
  simp at hr
  linarith

/-- A Hecke-equivariant reverse lift from the quartic eigenform lands on the
same simple lattice eigenline. Its degree-three and degree-four forward lifts
can therefore be evaluated for the *full* return vector. -/
theorem theta_chain_on_eigenline
    {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] (K : V →ₗ[ℂ] V)
    (upThree : V →ₗ[ℂ] U) (upFour : V →ₗ[ℂ] W)
    (d back : V) (ev : ℂ)
    (simple : ∀ v, K v = ev • v → ∃ c : ℂ, v = c • d)
    (returnedEigenvector : K back = ev • back) (hn : back ≠ 0)
    (hThree : upThree d = 0) (hFour : upFour d ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ back = c • d ∧ upThree back = 0 ∧
      upFour back = c • upFour d ∧ upFour back ≠ 0 := by
  obtain ⟨c, hc⟩ := simple back returnedEigenvector
  have hcn : c ≠ 0 := by
    intro he
    apply hn
    simpa [he] using hc
  refine ⟨c, hcn, hc, ?_, ?_, ?_⟩
  · simp [hc, hThree]
  · simp [hc]
  · simpa [hc] using smul_ne_zero hcn hFour

end CoxeterToddThetaChain
