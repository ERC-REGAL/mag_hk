import MagHK.PlanarSpectralLibrary
import MagHK.AxialRealization
import MagHK.ConcreteSlater

/-! Actual three-dimensional tensor realization relative to the general
selfadjoint tensor-sum theorem. The numerical spectral conclusions and the
identification of the manuscript's Cartesian orbitals are proved below.
-/
noncomputable section
namespace MagHK.TensorRealization
open MeasureTheory Set
open MagHK.Ordering MagHK.Noninteracting MagHK.RadialEndpoints MagHK.Cartesian
open scoped ContDiff ComplexConjugate

abbrev Space := ℂ × ℝ
abbrev State := Lp ℂ 2 (volume : Measure Space)
abbrev System := DomainOperator State

/-- An actual L² representative is an eigenfunction, not merely a label. -/
def EigenFunction (T : System) (E : ℝ) (f : Space → ℂ) : Prop :=
  ∃ ψ : State, (∀ᵐ x, ψ x = f x) ∧ OperatorModel.Eigen T E ψ

def differentialExpression (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ)
    (W : ℝ → ℝ) (η : Space → ℂ) (x : Space) : ℂ :=
  let dx := fun y => fderiv ℝ η y ((1 : ℂ), 0)
  let dy := fun y => fderiv ℝ η y (Complex.I, 0)
  let dz := fun y => fderiv ℝ η y ((0 : ℂ), 1)
  let az := A (x.1.re, x.1.im)
  show ℂ from -(fderiv ℝ dx x ((1 : ℂ), 0)) - fderiv ℝ dy x (Complex.I, 0) -
    fderiv ℝ dz x ((0 : ℂ), 1) -
    2 * Complex.I * ((az.1 : ℂ) * dx x + (az.2 : ℂ) * dy x) +
    ((az.1 ^ 2 + az.2 ^ 2 + V (x.1.re, x.1.im) + W x.2 : ℝ) : ℂ) * η x

/-- General tensor-sum laws, with both factors and the differential realization
visible. The separated-function rule is universal in all radial/axial states,
energies and scalar multiples. It assumes only the actual product formula. -/
structure Facts (T : System) (P : PlanarSpectralLibrary.System)
    (Z : AxialRealization.System) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) : Prop where
  selfadjoint : OperatorModel.SelfAdjoint T
  test_action : ∀ η : Space → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
    ∃ ψ : State, (∀ᵐ x, ψ x = η x) ∧ ∃ hψ : ψ ∈ T.domain,
      ∀ᵐ x, (T.map ⟨ψ, hψ⟩) x = differentialExpression A V W η x
  weak_equation : ∀ ψ (hψ : ψ ∈ T.domain) (η : Space → ℂ),
    ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ x, conj (η x) * (T.map ⟨ψ, hψ⟩) x) =
        ∫ x, conj (differentialExpression A V W η x) * ψ x
  spectrum_sum : ∀ E, E ∈ OperatorModel.spectrum T ↔
    ∃ p ∈ P.spectrum, ∃ z ∈ Z.spectrum, p + z = E
  unique_sum_dimension : ∀ e f,
    e ∈ P.spectrum → f ∈ Z.spectrum →
    (∀ p ∈ P.spectrum, ∀ z ∈ Z.spectrum, p + z = e + f → p = e ∧ z = f) →
    OperatorModel.multiplicity T (e + f) = P.multiplicity e * Z.multiplicity f
  separated_eigenfunction : ∀ (m : ℤ) (e f : ℝ) (u w : ℝ → ℝ)
      (ψ : RadialRealization.State) (ξ : AxialRealization.State)
      (g : Space → ℂ) (k : ℂ),
    RadialRealization.Eigen P.radial m e →
    AxialRealization.Eigen Z f ξ →
    (∀ᵐ r ∂RadialRealization.radialMeasure, ψ r = (u r : ℂ)) →
    (∃ h : ψ ∈ (P.radial.L m).domain,
      ψ ≠ 0 ∧ (P.radial.L m).map ⟨ψ, h⟩ = e • ψ) →
    (∀ᵐ z, ξ z = (w z : ℂ)) →
    (∀ r θ z, 0 < r → g (CartesianOrbitals.toCartesian (r, θ, z)) =
      k * (u r : ℂ) * Complex.exp (Complex.I * ((m : ℝ) * θ : ℝ)) * (w z : ℂ)) →
    k ≠ 0 → EigenFunction T (e + f) g

/-- Standard selfadjoint tensor sums of nonnegative factors. The universal
quantifiers prevent any manuscript-specific spectral conclusion being assumed. -/
def StandardTensorLibrary : Prop :=
  ∀ (P : PlanarSpectralLibrary.System) (Z : AxialRealization.System)
    (a v U : ℝ → ℝ) (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (Q W : ℝ → ℝ),
    PlanarSpectralLibrary.PlanarCoefficients a v A V → ContDiff ℝ ∞ W →
    PlanarSpectralLibrary.Facts P a v U A V → AxialRealization.Facts Z Q W →
    (∀ E ∈ P.spectrum, 0 ≤ E) → (∀ E ∈ Z.spectrum, 0 ≤ E) →
    ∃ T : System, Facts T P Z A V W

theorem spectrum_nonnegative (s : Set ℝ)
    (h : ∀ E, E ∈ s ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) : ∀ E ∈ s, 0 ≤ E := by
  intro E hE
  by_cases he : E ≤ 20
  · rcases (h E).mp ⟨hE, he⟩ with rfl | rfl <;> norm_num
  · linarith

/-- Elementary consequences of the general spectrum sum and dimension laws. -/
theorem tensor_levels (T : System) (P : PlanarSpectralLibrary.System)
    (Z : AxialRealization.System) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (hT : Facts T P Z A V W)
    (lam threshold : ℝ) (hlam : 0 < lam) (hc : lam < threshold)
    (hP : ∀ E, E ∈ P.spectrum ∧ E ≤ lam ↔ E = 0 ∨ E = lam)
    (hP0 : P.multiplicity 0 = 1) (hPlam : P.multiplicity lam = 1)
    (hgap : ∃ ε : ℝ, 0 < ε ∧ ∀ E, lam < E → E < lam + ε → E ∉ P.spectrum)
    (hZ0 : 0 ∈ Z.spectrum) (hZm : Z.multiplicity 0 = 1)
    (hZ : ∀ E ∈ Z.spectrum, E = 0 ∨ threshold ≤ E) :
    (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ lam ↔ E = 0 ∨ E = lam) ∧
    OperatorModel.multiplicity T 0 = 1 ∧ OperatorModel.multiplicity T lam = 1 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ E, lam < E → E < lam + ε → E ∉ OperatorModel.spectrum T := by
  have hpnon : ∀ E ∈ P.spectrum, 0 ≤ E := by
    intro E hE
    by_cases he : E ≤ lam
    · rcases (hP E).mp ⟨hE, he⟩ with rfl | rfl
      · exact le_rfl
      · exact hlam.le
    · linarith
  have hp0 : 0 ∈ P.spectrum := ((hP 0).mpr (Or.inl rfl)).1
  have hplam : lam ∈ P.spectrum := ((hP lam).mpr (Or.inr rfl)).1
  have unique : ∀ E, E ≤ lam → ∀ p ∈ P.spectrum, ∀ z ∈ Z.spectrum,
      p + z = E → p = E ∧ z = 0 := by
    intro E hE p hp z hz he
    rcases hZ z hz with hzero | hhigh
    · subst z
      simpa using he
    · have := hpnon p hp
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E
    constructor
    · rintro ⟨hE, he⟩
      obtain ⟨p, hp, z, hz, heq⟩ := (hT.spectrum_sum E).mp hE
      obtain ⟨hpE, _⟩ := unique E he p hp z hz heq
      rw [hpE] at hp
      exact (hP E).mp ⟨hp, he⟩
    · intro hE
      rcases hE with hzero | hsecond
      · subst E
        exact ⟨(hT.spectrum_sum 0).mpr ⟨0, hp0, 0, hZ0, by norm_num⟩, by positivity⟩
      · subst E
        exact ⟨(hT.spectrum_sum lam).mpr ⟨lam, hplam, 0, hZ0, by norm_num⟩, le_rfl⟩
  · have h := hT.unique_sum_dimension 0 0 hp0 hZ0
      (fun p hp z hz he => unique 0 (by positivity) p hp z hz (by simpa using he))
    simpa only [add_zero, hP0, hZm, one_mul] using h
  · have h := hT.unique_sum_dimension lam 0 hplam hZ0
      (fun p hp z hz he => unique lam le_rfl p hp z hz (by simpa using he))
    simpa only [add_zero, hPlam, hZm, one_mul] using h
  · obtain ⟨ε, hε, hg⟩ := hgap
    refine ⟨min ε (threshold - lam), lt_min hε (by linarith), ?_⟩
    intro E hE hEtop hEs
    obtain ⟨p, hp, z, hz, heq⟩ := (hT.spectrum_sum E).mp hEs
    rcases hZ z hz with hz0 | hzbig
    · subst z
      have hpE : p = E := by simpa using heq
      subst p
      apply hg E hE _ hp
      have := min_le_left ε (threshold - lam)
      linarith
    · have := hpnon p hp
      have := min_le_right ε (threshold - lam)
      linarith

/-- Elementary consequences of the general spectrum sum and dimension laws. -/
theorem bounded_tensor_levels (T : System) (P : PlanarSpectralLibrary.System)
    (Z : AxialRealization.System) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (hT : Facts T P Z A V W)
    (c : ℝ) (hc : 20 < c ^ 2)
    (hP : ∀ E, E ∈ P.spectrum ∧ E ≤ 20 ↔ E = 0 ∨ E = 20)
    (hP0 : P.multiplicity 0 = 1) (hP20 : P.multiplicity 20 = 1)
    (hgap : ∃ ε : ℝ, 0 < ε ∧ ∀ E, 20 < E → E < 20 + ε → E ∉ P.spectrum)
    (hZ0 : 0 ∈ Z.spectrum) (hZm : Z.multiplicity 0 = 1)
    (hZ : ∀ E ∈ Z.spectrum, E = 0 ∨ c ^ 2 ≤ E) :
    (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) ∧
    OperatorModel.multiplicity T 0 = 1 ∧ OperatorModel.multiplicity T 20 = 1 ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ E, 20 < E → E < 20 + ε → E ∉ OperatorModel.spectrum T := by
  have hpnon := spectrum_nonnegative P.spectrum hP
  have hp0 : 0 ∈ P.spectrum := ((hP 0).mpr (Or.inl rfl)).1
  have hp20 : 20 ∈ P.spectrum := ((hP 20).mpr (Or.inr rfl)).1
  have unique : ∀ E, E ≤ 20 → ∀ p ∈ P.spectrum, ∀ z ∈ Z.spectrum,
      p + z = E → p = E ∧ z = 0 := by
    intro E hE p hp z hz he
    rcases hZ z hz with hzero | hhigh
    · subst z
      simpa using he
    · have := hpnon p hp
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E
    constructor
    · rintro ⟨hE, he⟩
      obtain ⟨p, hp, z, hz, heq⟩ := (hT.spectrum_sum E).mp hE
      obtain ⟨hpE, _⟩ := unique E he p hp z hz heq
      rw [hpE] at hp
      exact (hP E).mp ⟨hp, he⟩
    · intro hE
      rcases hE with rfl | rfl
      · exact ⟨(hT.spectrum_sum 0).mpr ⟨0, hp0, 0, hZ0, by norm_num⟩, by norm_num⟩
      · exact ⟨(hT.spectrum_sum 20).mpr ⟨20, hp20, 0, hZ0, by norm_num⟩, le_rfl⟩
  · have h := hT.unique_sum_dimension 0 0 hp0 hZ0
      (fun p hp z hz he => unique 0 (by norm_num) p hp z hz (by simpa using he))
    simpa only [add_zero, hP0, hZm, one_mul] using h
  · have h := hT.unique_sum_dimension 20 0 hp20 hZ0
      (fun p hp z hz he => unique 20 le_rfl p hp z hz (by simpa using he))
    simpa only [add_zero, hP20, hZm, one_mul] using h
  · obtain ⟨ε, hε, hg⟩ := hgap
    refine ⟨min ε (c ^ 2 - 20), lt_min hε (by linarith), ?_⟩
    intro E hE hEtop hEs
    obtain ⟨p, hp, z, hz, heq⟩ := (hT.spectrum_sum E).mp hEs
    rcases hZ z hz with hz0 | hzbig
    · subst z
      have hpE : p = E := by simpa using heq
      subst p
      apply hg E hE _ hp
      have := min_le_left ε (c ^ 2 - 20)
      linarith
    · have := hpnon p hp
      have := min_le_right ε (c ^ 2 - 20)
      linarith

private theorem normalization_ne_zero (t : ℝ) (ht : 0 ≤ t) :
    (CylindricalOrbitals.normalization t : ℂ) ≠ 0 := by
  have h : 0 < 2 * Real.pi * radialNormF t := by
    have := radialNormF_pos t ht
    positivity
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr h))

theorem bounded_zero_eigenfunction (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (P : PlanarSpectralLibrary.System) (Z : AxialRealization.System) (T : System)
    (hP : PlanarSpectralLibrary.Facts P (profileA t) (regularProfileV t) (profileU t)
      (boundedVector t) (boundedScalar t))
    (hz : AxialRealization.Eigen Z 0 (AxialRealization.chiState c hc))
    (hT : Facts T P Z (boundedVector t) (boundedScalar t) (Axial.potential c)) :
    EigenFunction T 0 (CartesianOrbitals.orbitalZero t c) := by
  have hs := BoundedRealization.bounded_zero_solution t ht
  obtain ⟨hd, he⟩ := hP.radial_facts.regular_solution
    (BoundedRealization.bounded_coefficients t ht) 0 0 _ _ hs
  have hei : RadialRealization.Eigen P.radial 0 0 := ⟨_, hd, hs.nonzero, he⟩
  have hout := hT.separated_eigenfunction 0 0 0 (profileF t) (Axial.chi c)
    (BoundedRealization.zeroState t ht.le) (AxialRealization.chiState c hc)
    (CartesianOrbitals.orbitalZero t c) (CylindricalOrbitals.normalization t)
    hei hz hs.represented ⟨hd, hs.nonzero, he⟩
    (AxialRealization.chi_memLp c hc).coeFn_toLp ?_ (normalization_ne_zero t ht.le)
  · simpa only [add_zero] using hout
  · intro r θ z hr
    rw [CartesianOrbitals.orbitalZero_pullback t c (r, θ, z) hr.le]
    simp [CylindricalOrbitals.orbitalZero, CylindricalOrbitals.radialZero]

theorem bounded_minus_eigenfunction (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (P : PlanarSpectralLibrary.System) (Z : AxialRealization.System) (T : System)
    (hP : PlanarSpectralLibrary.Facts P (profileA t) (regularProfileV t) (profileU t)
      (boundedVector t) (boundedScalar t))
    (hz : AxialRealization.Eigen Z 0 (AxialRealization.chiState c hc))
    (hT : Facts T P Z (boundedVector t) (boundedScalar t) (Axial.potential c)) :
    EigenFunction T 20 (CartesianOrbitals.orbitalMinus t c) := by
  have hs := BoundedRealization.bounded_minus_solution t ht
  obtain ⟨hd, he⟩ := hP.radial_facts.regular_solution
    (BoundedRealization.bounded_coefficients t ht) (-1) 20 _ _ hs
  have hei : RadialRealization.Eigen P.radial (-1) 20 := ⟨_, hd, hs.nonzero, he⟩
  have hk : (CylindricalOrbitals.normalization t : ℂ) * (Real.sqrt t : ℂ) ≠ 0 :=
    mul_ne_zero (normalization_ne_zero t ht.le)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr ht))
  have hout := hT.separated_eigenfunction (-1) 20 0 (SecondOrbital.boundedProduct t) (Axial.chi c)
    (BoundedRealization.minusState t ht.le) (AxialRealization.chiState c hc)
    (CartesianOrbitals.orbitalMinus t c)
    ((CylindricalOrbitals.normalization t : ℂ) * (Real.sqrt t : ℂ))
    hei hz hs.represented ⟨hd, hs.nonzero, he⟩
    (AxialRealization.chi_memLp c hc).coeFn_toLp ?_ hk
  · simpa only [add_zero] using hout
  · intro r θ z hr
    rw [CartesianOrbitals.orbitalMinus_pullback t c (r, θ, z) hr.le]
    simp only [CylindricalOrbitals.orbitalMinus, CylindricalOrbitals.radialMinus,
      CylindricalOrbitals.phase_eq_negative_exp, SecondOrbital.boundedProduct,
      Complex.ofReal_mul, Int.cast_neg, Int.cast_one, neg_one_mul, Complex.ofReal_neg]
    simp only [neg_mul, mul_neg, mul_comm Complex.I (θ : ℂ)]
    ring

end MagHK.TensorRealization
