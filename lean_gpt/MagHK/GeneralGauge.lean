import MagHK.ManyBodyTimeReversal
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Smooth scalar gauges for arbitrary finite particle number. All phase,
momentum, form, density and current identities are literal function identities.
The operator interface uses actual unitary multiplication and the inverse-image
operator domain. Its external results are the general unitary multiplication,
closed-form representation and spectral transport theorems.
-/
noncomputable section
namespace MagHK.GeneralGauge
open MeasureTheory Set Filter
open MagHK.ManyBodyTimeReversal
open scoped ContDiff ComplexConjugate BigOperators
set_option maxHeartbeats 1000000

def totalPhase (N : ℕ) (η : Point → ℝ) (x : Configuration N) : ℝ := ∑ i, η (x i)
def phase (N : ℕ) (η : Point → ℝ) (x : Configuration N) : ℂ :=
  Complex.exp (-Complex.I * (totalPhase N η x : ℂ))
def wave (N : ℕ) (η : Point → ℝ) (f : Configuration N → ℂ) (x : Configuration N) : ℂ :=
  phase N η x * f x
def gradient (η : Point → ℝ) (x : Point) (k : Fin 3) : ℝ :=
  fderiv ℝ η x (Pi.single k 1)

theorem phase_norm (N : ℕ) (η : Point → ℝ) (x : Configuration N) : ‖phase N η x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_normSq (N : ℕ) (η : Point → ℝ) (x : Configuration N) :
    Complex.normSq (phase N η x) = 1 := by rw [Complex.normSq_eq_norm_sq, phase_norm]; norm_num

theorem phase_conj_mul (N : ℕ) (η : Point → ℝ) (x : Configuration N) :
    conj (phase N η x) * phase N η x = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, phase_normSq]
  rfl

theorem totalPhase_contDiff (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (totalPhase N η) := by
  apply ContDiff.sum
  intro i _
  exact hη.comp (contDiff_apply ℝ Point i)

theorem phase_contDiff (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (phase N η) := by
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (totalPhase_contDiff N η hη))).cexp

theorem totalPhase_permute (N : ℕ) (η : Point → ℝ) (σ : Equiv.Perm (Fin N))
    (x : Configuration N) : totalPhase N η (permute N σ x) = totalPhase N η x := by
  unfold totalPhase
  calc
    _ = ∑ i : Fin N, η (permute N σ x (σ i)) := (Equiv.sum_comp σ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [permute, MeasurableEquiv.piCongrLeft_apply_apply]

theorem phase_permute (N : ℕ) (η : Point → ℝ) (σ : Equiv.Perm (Fin N))
    (x : Configuration N) : phase N η (permute N σ x) = phase N η x := by
  simp only [phase, totalPhase_permute]

theorem core_wave (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (f : Configuration N → ℂ) (hf : Core N f) : Core N (wave N η f) := by
  refine ⟨(phase_contDiff N η hη).mul hf.1, hf.2.1.mul_left, ?_⟩
  intro σ x
  dsimp only [wave]
  rw [phase_permute, hf.2.2 σ x]
  ring

theorem totalPhase_derivative (N : ℕ) (η : Point → ℝ) (hη : Differentiable ℝ η)
    (x : Configuration N) (i : Fin N) (k : Fin 3) :
    fderiv ℝ (totalPhase N η) x (direction N i k) = gradient η (x i) k := by
  have h : HasFDerivAt (totalPhase N η)
      (∑ j : Fin N, (fderiv ℝ η (x j)).comp (ContinuousLinearMap.proj j)) x := by
    have hj (j : Fin N) : HasFDerivAt (fun y : Configuration N => η (y j))
        ((fderiv ℝ η (x j)).comp (ContinuousLinearMap.proj j)) x :=
      (hη (x j)).hasFDerivAt.comp x
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Point) j).hasFDerivAt
    have hfun : (∑ j : Fin N, fun y : Configuration N => η (y j)) = totalPhase N η := by
      funext y
      simp [totalPhase]
    rw [← hfun]
    exact HasFDerivAt.sum (u := Finset.univ) (fun j _ => hj j)
  rw [h.fderiv]
  simp [direction, gradient, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    Pi.single_apply, apply_ite]

theorem phase_derivative (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (x : Configuration N) (i : Fin N) (k : Fin 3) :
    fderiv ℝ (phase N η) x (direction N i k) =
      -Complex.I * (gradient η (x i) k : ℂ) * phase N η x := by
  have ht := (totalPhase_contDiff N η hη).differentiable (by norm_num) x
  have hd := ((Complex.ofRealCLM.hasFDerivAt.comp x ht.hasFDerivAt).const_mul (-Complex.I)).cexp
  change HasFDerivAt (phase N η) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Function.comp_apply]
  rw [totalPhase_derivative N η (hη.differentiable (by norm_num))]
  dsimp only [phase]
  ring

theorem momentum_gauge (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (A : Point → Point) (f : Configuration N → ℂ) (hf : Differentiable ℝ f)
    (x : Configuration N) (i : Fin N) (k : Fin 3) :
    momentum N (A + gradient η) (wave N η f) i k x =
      phase N η x * momentum N A f i k x := by
  have hp := (phase_contDiff N η hη).differentiable (by norm_num) x
  have hd := hp.hasFDerivAt.mul (hf x).hasFDerivAt
  change HasFDerivAt (fun y => phase N η y * f y) _ x at hd
  unfold momentum wave
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Pi.add_apply, Complex.ofReal_add]
  rw [phase_derivative N η hη]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem form_gauge (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (A : Point → Point) (V : Configuration N → ℝ)
    (f g : Configuration N → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    form N (A + gradient η) V (wave N η f) (wave N η g) = form N A V f g := by
  unfold form
  apply integral_congr_ae
  filter_upwards [] with x
  simp_rw [momentum_gauge N η hη A f hf, momentum_gauge N η hη A g hg]
  have hkin (i : Fin N) (k : Fin 3) :
      conj (phase N η x * momentum N A f i k x) *
        (phase N η x * momentum N A g i k x) =
      conj (momentum N A f i k x) * momentum N A g i k x := by
    rw [map_mul]
    calc
      _ = (conj (phase N η x) * phase N η x) *
        (conj (momentum N A f i k x) * momentum N A g i k x) := by ring
      _ = _ := by rw [phase_conj_mul, one_mul]
  simp_rw [hkin]
  congr 1
  simp only [wave, map_mul]
  calc
    _ = (conj (phase N η x) * phase N η x) * ((V x : ℂ) * conj (f x) * g x) := by ring
    _ = _ := by rw [phase_conj_mul, one_mul]

theorem density_gauge (N : ℕ) (η : Point → ℝ) (f : Configuration (N + 1) → ℂ) :
    density N (wave (N + 1) η f) = density N f := by
  funext x
  simp [density, wave, Complex.normSq_mul, phase_normSq]

theorem current_gauge (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (A : Point → Point) (f : Configuration (N + 1) → ℂ) (hf : Differentiable ℝ f) :
    current N (A + gradient η) (wave (N + 1) η f) = current N A f := by
  funext x k
  unfold current
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  rw [momentum_gauge (N + 1) η hη A f hf]
  unfold wave
  have he : conj (phase (N + 1) η (Fin.cons x y) * f (Fin.cons x y)) *
      (phase (N + 1) η (Fin.cons x y) * momentum (N + 1) A f 0 k (Fin.cons x y)) =
      conj (f (Fin.cons x y)) * momentum (N + 1) A f 0 k (Fin.cons x y) := by
    rw [map_mul]
    calc
      _ = (conj (phase (N + 1) η (Fin.cons x y)) * phase (N + 1) η (Fin.cons x y)) *
        (conj (f (Fin.cons x y)) * momentum (N + 1) A f 0 k (Fin.cons x y)) := by ring
      _ = _ := by rw [phase_conj_mul, one_mul]
  rw [he]

structure PhaseUnitary (N : ℕ) (η : Point → ℝ) where
  map : State N ≃ₗᵢ[ℝ] State N
  complex_linear : ∀ c : ℂ, ∀ ψ : State N, map (c • ψ) = c • map ψ
  represented : ∀ ψ : State N, ∀ᵐ x,
    (map ψ : FullState N) x = wave N η (ψ : FullState N) x

/-- Multiplication by a symmetric unit-modulus function is unitary on the
antisymmetric L² subspace. The multiplier is explicitly fixed here. -/
def StandardPhaseMultiplierLibrary : Prop :=
  ∀ N η, ContDiff ℝ ∞ η → Nonempty (PhaseUnitary N η)

def gaugeOperator (N : ℕ) (U : State N ≃ₗᵢ[ℝ] State N) (H : System N) : System N where
  domain := H.domain.comap U.symm.toLinearEquiv.toLinearMap
  map :=
    { toFun := fun ψ => U (H.map ⟨U.symm ψ, ψ.property⟩)
      map_add' := by
        intro ψ φ
        simp only [Submodule.coe_add, map_add]
        change U (H.map (⟨U.symm ψ, ψ.property⟩ + ⟨U.symm φ, φ.property⟩)) = _
        rw [map_add, map_add]
      map_smul' := by
        intro c ψ
        simp only [Submodule.coe_smul, map_smul]
        change U (H.map (c • ⟨U.symm ψ, ψ.property⟩)) = _
        rw [map_smul, map_smul]
        rfl }

theorem gauge_domain (N : ℕ) (U : State N ≃ₗᵢ[ℝ] State N) (H : System N) (ψ : State N) :
    U ψ ∈ (gaugeOperator N U H).domain ↔ ψ ∈ H.domain := by
  change U.symm (U ψ) ∈ H.domain ↔ _
  rw [U.symm_apply_apply]

theorem gauge_action (N : ℕ) (U : State N ≃ₗᵢ[ℝ] State N) (H : System N)
    (ψ : State N) (hψ : ψ ∈ H.domain) :
    (gaugeOperator N U H).map ⟨U ψ, (gauge_domain N U H ψ).mpr hψ⟩ = U (H.map ⟨ψ, hψ⟩) := by
  change U (H.map ⟨U.symm (U ψ), _⟩) = _
  simp only [U.symm_apply_apply]

theorem gauge_eigen (N : ℕ) (U : State N ≃ₗᵢ[ℝ] State N) (H : System N)
    (E : ℝ) (ψ : State N) (hψ : OperatorModel.Eigen H E ψ) :
    OperatorModel.Eigen (gaugeOperator N U H) E (U ψ) := by
  obtain ⟨hd, hn, he⟩ := hψ
  refine ⟨(gauge_domain N U H ψ).mpr hd, ?_, ?_⟩
  · exact fun hz => hn (U.injective (by simpa only [map_zero] using hz))
  · rw [gauge_action N U H ψ hd, he, map_smul]

/-- General unitary transport of a Friedrichs integral form and its spectrum.
The concrete form identity is an argument, proved in `form_gauge`. -/
def StandardUnitaryFormLibrary : Prop :=
  ∀ N η (hη : ContDiff ℝ ∞ η) (U : PhaseUnitary N η) (H : System N) A V b,
    Facts N H A V b →
    (∀ f, Core N f → Core N (wave N η f)) →
    (∀ f g, Core N f → Core N g →
      form N (A + gradient η) (fun x => V x + b) (wave N η f) (wave N η g) =
        form N A (fun x => V x + b) f g) →
    Facts N (gaugeOperator N U.map H) (A + gradient η) V b ∧
      OperatorModel.spectrum (gaugeOperator N U.map H) = OperatorModel.spectrum H ∧
      OperatorModel.multiplicity (gaugeOperator N U.map H) = OperatorModel.multiplicity H

theorem gauge_realization (multipliers : StandardPhaseMultiplierLibrary)
    (transport : StandardUnitaryFormLibrary) (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (H : System N) (A : Point → Point) (V : Configuration N → ℝ) (b : ℝ)
    (hH : Facts N H A V b) :
    ∃ U : PhaseUnitary N η, Facts N (gaugeOperator N U.map H) (A + gradient η) V b ∧
      OperatorModel.spectrum (gaugeOperator N U.map H) = OperatorModel.spectrum H ∧
      OperatorModel.multiplicity (gaugeOperator N U.map H) = OperatorModel.multiplicity H := by
  obtain ⟨U⟩ := multipliers N η hη
  refine ⟨U, transport N η hη U H A V b hH (core_wave N η hη) ?_⟩
  intro f g hf hg
  exact form_gauge N η hη A _ f g
    (hf.1.differentiable (by norm_num)) (hg.1.differentiable (by norm_num))

def shiftOperator (N : ℕ) (H : System N) (c : ℝ) : System N where
  domain := H.domain
  map := H.map + c • H.domain.subtype

theorem shift_eigen_iff (N : ℕ) (H : System N) (c E : ℝ) (ψ : State N) :
    OperatorModel.Eigen (shiftOperator N H c) (E + c) ψ ↔ OperatorModel.Eigen H E ψ := by
  constructor
  · rintro ⟨hψ, hn, he⟩
    refine ⟨hψ, hn, ?_⟩
    change H.map ⟨ψ, hψ⟩ + c • ψ = (E + c) • ψ at he
    rw [add_smul] at he
    exact add_right_cancel he
  · rintro ⟨hψ, hn, he⟩
    refine ⟨hψ, hn, ?_⟩
    change H.map ⟨ψ, hψ⟩ + c • ψ = (E + c) • ψ
    rw [he, add_smul]

theorem hamiltonianPotential_shift (N : ℕ) (v : Point → ℝ) (κ c : ℝ) :
    hamiltonianPotential N (fun x => v x + c) κ = fun x => hamiltonianPotential N v κ x + N * c := by
  funext x
  simp [hamiltonianPotential, Finset.sum_add_distrib]
  ring

end MagHK.GeneralGauge
