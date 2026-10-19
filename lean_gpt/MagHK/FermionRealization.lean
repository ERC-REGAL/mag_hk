import MagHK.TensorRealization

/-!
The bounded noninteracting ground state relative to standard exterior-power
operator theory. The fermionic Hilbert space is the actual antisymmetric
subspace of Lebesgue L² on two copies of ℂ×ℝ. The library premise is the
universal two-level filling theorem, including the actual weak differential
sum realization. All profile, parameter, spectrum-ordering, normalized orbital,
and determinant-identification inputs for the manuscript are proved.
-/
noncomputable section
namespace MagHK.FermionRealization
open MeasureTheory Set
open MagHK.Ordering MagHK.TensorRealization
open scoped ContDiff ComplexConjugate

abbrev PairState := Lp ℂ 2 (volume : Measure (Space × Space))

def swap : PairState →ₗᵢ[ℂ] PairState :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.swap Measure.measurePreserving_swap

/-- Kernel of swap+identity, hence literal antisymmetric two-particle L². -/
def fermionSubspace : Submodule ℂ PairState :=
  (swap.toLinearMap + LinearMap.id).ker

abbrev FermionState := fermionSubspace
abbrev System := DomainOperator FermionState

structure OneBodyRealization (T : TensorRealization.System)
    (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) : Prop where
  selfadjoint : OperatorModel.SelfAdjoint T
  test_action : ∀ η : Space → ℂ, ContDiff ℝ ∞ η → HasCompactSupport η →
    ∃ ψ : TensorRealization.State, (∀ᵐ x, ψ x = η x) ∧ ∃ hψ : ψ ∈ T.domain,
      ∀ᵐ x, (T.map ⟨ψ, hψ⟩) x = TensorRealization.differentialExpression A V W η x
  weak_equation : ∀ ψ (hψ : ψ ∈ T.domain) (η : Space → ℂ),
    ContDiff ℝ ∞ η → HasCompactSupport η →
      (∫ x, conj (η x) * (T.map ⟨ψ, hψ⟩) x) =
        ∫ x, conj (TensorRealization.differentialExpression A V W η x) * ψ x

def differentialExpression (A : ℝ × ℝ → ℝ × ℝ) (V : ℝ × ℝ → ℝ)
    (W : ℝ → ℝ) (η : Space × Space → ℂ) (p : Space × Space) : ℂ :=
  TensorRealization.differentialExpression A V W (fun x => η (x, p.2)) p.1 +
    TensorRealization.differentialExpression A V W (fun y => η (p.1, y)) p.2

structure Facts (F : System) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ) : Prop where
  selfadjoint : OperatorModel.SelfAdjoint F
  test_action : ∀ η : Space × Space → ℂ,
    ContDiff ℝ ∞ η → HasCompactSupport η → (∀ x y, η (y, x) = -η (x, y)) →
    ∃ ψ : FermionState, (∀ᵐ p, (ψ : PairState) p = η p) ∧ ∃ hψ : ψ ∈ F.domain,
      ∀ᵐ p, ((F.map ⟨ψ, hψ⟩ : FermionState) : PairState) p = differentialExpression A V W η p
  weak_equation : ∀ ψ (hψ : ψ ∈ F.domain) (η : Space × Space → ℂ),
    ContDiff ℝ ∞ η → HasCompactSupport η → (∀ x y, η (y, x) = -η (x, y)) →
      (∫ p, conj (η p) * ((F.map ⟨ψ, hψ⟩ : FermionState) : PairState) p) =
        ∫ p, conj (differentialExpression A V W η p) * (ψ : PairState) p

/-- The actual representative spans the isolated eigenspace at the spectral bottom. -/
def GroundState (F : System) (E : ℝ) (f : Space × Space → ℂ) : Prop :=
  (∃ ψ : FermionState, (∀ᵐ p, (ψ : PairState) p = f p) ∧ OperatorModel.Eigen F E ψ) ∧
  (∀ e ∈ OperatorModel.spectrum F, E ≤ e) ∧ OperatorModel.multiplicity F E = 1 ∧
  ∃ ε : ℝ, 0 < ε ∧ ∀ e ∈ OperatorModel.spectrum F, |e - E| < ε → e = E

def determinant (f g : Space → ℂ) (p : Space × Space) : ℂ :=
  MagHK.Slater.slaterSlice (f p.1) (g p.1) f g p.2

/-- Standard exterior-square filling for arbitrary isolated simple first two
levels. It includes construction of the selfadjoint operator on the literal
antisymmetric subspace and its weak differential sum law. This is a general
operator-theory premise, not a premise about the selected functions or levels.
-/
def StandardFermionLibrary : Prop :=
  ∀ (T : TensorRealization.System) (A : ℝ × ℝ → ℝ × ℝ)
    (V : ℝ × ℝ → ℝ) (W : ℝ → ℝ),
    OneBodyRealization T A V W →
    ∀ (e₀ e₁ : ℝ) (f g : Space → ℂ), e₀ < e₁ →
    (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ e₁ ↔ E = e₀ ∨ E = e₁) →
    OperatorModel.multiplicity T e₀ = 1 → OperatorModel.multiplicity T e₁ = 1 →
    (∃ ε : ℝ, 0 < ε ∧ ∀ E, e₁ < E → E < e₁ + ε → E ∉ OperatorModel.spectrum T) →
    EigenFunction T e₀ f → EigenFunction T e₁ g → MagHK.Slater.OrthonormalPair volume f g →
    ∃ F : System, Facts F A V W ∧ GroundState F (e₀ + e₁) (determinant f g)

/-- The literal bounded Slater determinant is the unique two-fermion ground
state and has positive density and zero physical current. The only external
premises are the four universal standard operator-theory libraries documented
above. In particular no radial ordering, chosen-orbital eigenstate, or chosen
Slater ground-state assertion is a premise. -/
theorem bounded_ground_state
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : AxialRealization.StandardAxialLibrary)
    (tensor : StandardTensorLibrary) (fermion : StandardFermionLibrary)
    (c : ℝ) (hc : 0 < c) (hgap : 20 < c ^ 2) :
    ∃ t : ℝ, 0 < t ∧ ∃ T : TensorRealization.System, ∃ F : System,
      OneBodyRealization T (Cartesian.boundedVector t) (Cartesian.boundedScalar t) (Axial.potential c) ∧
      (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) ∧
      OperatorModel.multiplicity T 0 = 1 ∧ OperatorModel.multiplicity T 20 = 1 ∧
      Facts F (Cartesian.boundedVector t) (Cartesian.boundedScalar t) (Axial.potential c) ∧
      GroundState F 20 (fun p => ConcreteSlater.wave t c p.1 p.2) ∧
      (∫ p : Space × Space, Complex.normSq (ConcreteSlater.wave t c p.1 p.2)) = 1 ∧
      (∀ x, 0 < 2 * ∫ y, Complex.normSq (ConcreteSlater.wave t c x y)) ∧
      (∀ᵐ x : Space, ∀ d : Space, ConcreteSlater.physicalCurrent t c x d = 0) := by
  obtain ⟨t, ht, heq, _⟩ := MagHK.Noninteracting.exists_bounded_parameter
  obtain ⟨P, hP, hlevels, hp0, hp20, hpgap⟩ :=
    PlanarSpectralLibrary.bounded_planar_realization planar t ht
  obtain ⟨Z, hZ, hz, hz0, hzm, hzgap⟩ := AxialRealization.bounded_axial_realization axial c hc
  obtain ⟨T, hT⟩ := tensor P Z _ _ _ _ _ _ _
    (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (AxialRealization.bounded_coefficients c).V_smooth hP hZ
    (spectrum_nonnegative P.spectrum hlevels) hZ.nonnegative
  have h1 : OneBodyRealization T (Cartesian.boundedVector t) (Cartesian.boundedScalar t)
      (Axial.potential c) := ⟨hT.selfadjoint, hT.test_action, hT.weak_equation⟩
  obtain ⟨hle, hm0, hm20, htg⟩ := bounded_tensor_levels T P Z _ _ _ hT c hgap
    hlevels hp0 hp20 hpgap hz0 hzm hzgap
  have hzero := bounded_zero_eigenfunction t c ht hc P Z T hP hz hT
  have hminus := bounded_minus_eigenfunction t c ht hc P Z T hP hz hT
  have ho := CartesianOrbitals.bounded_orthonormal t c ht hc heq
  obtain ⟨F, hF, hg⟩ := fermion T _ _ _ h1 0 20 _ _ (by norm_num)
    hle hm0 hm20 htg hzero hminus ho
  refine ⟨t, ht, T, F, h1, hle, hm0, hm20, hF, ?_,
    ConcreteSlater.wave_normalized t c ht.le ho, ?_,
    ConcreteSlater.physicalCurrent_zero_ae t c ht.le ho⟩
  · simpa only [zero_add] using! hg
  · intro x
    rw [ConcreteSlater.wave_density_marginal t c ho x]
    exact ConcreteSlater.density_pos t c ht.le hc x

/-- A concrete bounded example with axial parameter c=5. The functions are
smooth and globally bounded, their magnetic curvature is nonzero, and the
literal Slater determinant is the unique ground state with zero current. -/
theorem bounded_example
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : AxialRealization.StandardAxialLibrary)
    (tensor : StandardTensorLibrary) (fermion : StandardFermionLibrary) :
    ∃ t : ℝ, 0 < t ∧
      ContDiff ℝ ∞ (ConstructionData.bounded3Vector t) ∧
      ContDiff ℝ ∞ (ConstructionData.bounded3Scalar t 5) ∧
      (∃ C : ℝ, ∀ p, ‖ConstructionData.bounded3Vector t p‖ ≤ C) ∧
      (∃ C : ℝ, ∀ p, |ConstructionData.bounded3Scalar t 5 p| ≤ C) ∧
      Cartesian.planarCurl (Cartesian.boundedVector t) ≠ 0 ∧
      ∃ T : TensorRealization.System, ∃ F : System,
      OneBodyRealization T (Cartesian.boundedVector t) (Cartesian.boundedScalar t) (Axial.potential 5) ∧
      (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) ∧
      OperatorModel.multiplicity T 0 = 1 ∧ OperatorModel.multiplicity T 20 = 1 ∧
      Facts F (Cartesian.boundedVector t) (Cartesian.boundedScalar t) (Axial.potential 5) ∧
      GroundState F 20 (fun p => ConcreteSlater.wave t 5 p.1 p.2) ∧
      (∫ p : Space × Space, Complex.normSq (ConcreteSlater.wave t 5 p.1 p.2)) = 1 ∧
      (∀ x, 0 < 2 * ∫ y, Complex.normSq (ConcreteSlater.wave t 5 x y)) ∧
      (∀ᵐ x : Space, ∀ d : Space, ConcreteSlater.physicalCurrent t 5 x d = 0) := by
  obtain ⟨t, ht, h⟩ := bounded_ground_state planar axial tensor fermion
    5 (by norm_num) (by norm_num)
  exact ⟨t, ht, ConstructionData.bounded3Vector_smooth t ht.le,
    ConstructionData.bounded3Scalar_smooth t 5 ht.le,
    ⟨t * Real.exp 2 + 1, ConstructionData.bounded3Vector_bound t ht.le⟩,
    ConstructionData.bounded3Scalar_bounded t 5 ht, Cartesian.bounded_curl_nonzero t ht, h⟩

end MagHK.FermionRealization
