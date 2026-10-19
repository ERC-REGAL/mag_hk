import MagHK.GeneralGauge

/-! The gauge law on the literal weak covariant derivative domain. Complex
compact tests are obtained from their real and imaginary parts. No smoothness
of the wavefunction or additional regularity theorem is used. -/
noncomputable section
namespace MagHK.GeneralGauge
open MeasureTheory Set Filter
open MagHK.ManyBodyTimeReversal
open scoped ComplexConjugate BigOperators ContDiff ENNReal
set_option maxHeartbeats 1000000

theorem weakMomentum_complex_test (N : ℕ) (A : Point → Point)
    (f : Configuration N → ℂ) (p : Fin N → Fin 3 → Configuration N → ℂ)
    (hp : WeakMomentum N A f p) (i : Fin N) (k : Fin 3)
    (ζ : Configuration N → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) :
    Integrable (fun x => p i k x * ζ x) ∧
    Integrable (fun x => Complex.I * f x * fderiv ℝ ζ x (direction N i k) +
      (A (x i) k : ℂ) * f x * ζ x) ∧
    (∫ x, p i k x * ζ x) =
      ∫ x, Complex.I * f x * fderiv ℝ ζ x (direction N i k) + (A (x i) k : ℂ) * f x * ζ x := by
  have hr := hp i k (fun x => (ζ x).re) (Complex.reCLM.contDiff.comp hζ)
    (hc.comp_left (by simp))
  have hi := hp i k (fun x => (ζ x).im) (Complex.imCLM.contDiff.comp hζ)
    (hc.comp_left (by simp))
  have hdre (x : Configuration N) : fderiv ℝ (fun y => (ζ y).re) x (direction N i k) =
      (fderiv ℝ ζ x (direction N i k)).re := by
    have h : HasFDerivAt (fun y => (ζ y).re) (Complex.reCLM.comp (fderiv ℝ ζ x)) x :=
      Complex.reCLM.hasFDerivAt.comp x ((hζ.differentiable (by norm_num)) x).hasFDerivAt
    rw [h.fderiv]
    rfl
  have hdim (x : Configuration N) : fderiv ℝ (fun y => (ζ y).im) x (direction N i k) =
      (fderiv ℝ ζ x (direction N i k)).im := by
    have h : HasFDerivAt (fun y => (ζ y).im) (Complex.imCLM.comp (fderiv ℝ ζ x)) x :=
      Complex.imCLM.hasFDerivAt.comp x ((hζ.differentiable (by norm_num)) x).hasFDerivAt
    rw [h.fderiv]
    rfl
  have hl (x : Configuration N) : p i k x * ζ x =
      p i k x * ((ζ x).re : ℂ) + Complex.I * (p i k x * ((ζ x).im : ℂ)) := by
    nth_rw 1 [← Complex.re_add_im (ζ x)]
    ring
  have hright (x : Configuration N) :
      Complex.I * f x * fderiv ℝ ζ x (direction N i k) + (A (x i) k : ℂ) * f x * ζ x =
      (Complex.I * f x * (fderiv ℝ (fun y => (ζ y).re) x (direction N i k) : ℂ) +
        (A (x i) k : ℂ) * f x * ((ζ x).re : ℂ)) +
      Complex.I * (Complex.I * f x * (fderiv ℝ (fun y => (ζ y).im) x (direction N i k) : ℂ) +
        (A (x i) k : ℂ) * f x * ((ζ x).im : ℂ)) := by
    rw [hdre, hdim]
    nth_rw 1 [← Complex.re_add_im (fderiv ℝ ζ x (direction N i k))]
    nth_rw 1 [← Complex.re_add_im (ζ x)]
    ring
  simp_rw [hl, hright]
  refine ⟨hr.1.add (hi.1.const_mul _), hr.2.1.add (hi.2.1.const_mul _), ?_⟩
  rw [integral_add hr.1 (hi.1.const_mul _), integral_add hr.2.1 (hi.2.1.const_mul _),
    integral_const_mul, integral_const_mul, hr.2.2, hi.2.2]

set_option maxHeartbeats 4000000 in
theorem weakMomentum_gauge (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (A : Point → Point) (f : Configuration N → ℂ)
    (p : Fin N → Fin 3 → Configuration N → ℂ) (hp : WeakMomentum N A f p) :
    WeakMomentum N (A + gradient η) (wave N η f) (fun i k => wave N η (p i k)) := by
  intro i k χ hχ hc
  let ζ : Configuration N → ℂ := fun x => phase N η x * (χ x : ℂ)
  have hz : ContDiff ℝ ∞ ζ := (phase_contDiff N η hη).mul (Complex.ofRealCLM.contDiff.comp hχ)
  have hχc : HasCompactSupport (fun x => (χ x : ℂ)) :=
    hc.comp_left (show ((0 : ℝ) : ℂ) = 0 from rfl)
  have hzc : HasCompactSupport ζ := hχc.mul_left
  obtain ⟨hl, hr, he⟩ := weakMomentum_complex_test N A f p hp i k ζ hz hzc
  have hd (x : Configuration N) : fderiv ℝ ζ x (direction N i k) =
      phase N η x * (fderiv ℝ χ x (direction N i k) : ℂ) +
      (-Complex.I * (gradient η (x i) k : ℂ) * phase N η x) * (χ x : ℂ) := by
    have h := (((phase_contDiff N η hη).differentiable (by norm_num) x).hasFDerivAt).mul
      (Complex.ofRealCLM.hasFDerivAt.comp x ((hχ.differentiable (by norm_num)) x).hasFDerivAt)
    change HasFDerivAt ζ _ x at h
    rw [h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Function.comp_apply, smul_eq_mul]
    rw [phase_derivative N η hη]
    ring
  have hleft (x : Configuration N) : wave N η (p i k) x * (χ x : ℂ) = p i k x * ζ x := by
    dsimp only [wave, ζ]
    ring
  have hright (x : Configuration N) :
      Complex.I * wave N η f x * (fderiv ℝ χ x (direction N i k) : ℂ) +
        ((A + gradient η) (x i) k : ℂ) * wave N η f x * (χ x : ℂ) =
      Complex.I * f x * fderiv ℝ ζ x (direction N i k) + (A (x i) k : ℂ) * f x * ζ x := by
    rw [hd]
    simp only [wave, ζ, Pi.add_apply, Complex.ofReal_add]
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp_rw [hleft, hright]
  exact ⟨hl, hr, he⟩

theorem weakCurrent_gauge (N : ℕ) (η : Point → ℝ)
    (f : Configuration (N + 1) → ℂ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ) :
    weakCurrent N (wave (N + 1) η f) (fun i k => wave (N + 1) η (p i k)) =
      weakCurrent N f p := by
  funext x k
  unfold weakCurrent
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  have he : conj (wave (N + 1) η f (Fin.cons x y)) *
      wave (N + 1) η (p 0 k) (Fin.cons x y) = conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y) := by
    dsimp only [wave]
    rw [map_mul]
    calc
      _ = (conj (phase (N + 1) η (Fin.cons x y)) * phase (N + 1) η (Fin.cons x y)) *
          (conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y)) := by ring
      _ = _ := by rw [phase_conj_mul, one_mul]
  rw [he]

theorem wave_memLp (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (f : Configuration N → ℂ) {p : ℝ≥0∞} (hf : MemLp f p) : MemLp (wave N η f) p := by
  apply hf.of_le_mul ((phase_contDiff N η hη).continuous.aestronglyMeasurable.mul hf.1) (c := 1)
  filter_upwards [] with x
  change ‖phase N η x * f x‖ ≤ 1 * ‖f x‖
  simp only [norm_mul, phase_norm, one_mul]
  exact le_rfl

theorem gauge_with_weak_current
    (multipliers : StandardPhaseMultiplierLibrary) (transport : StandardUnitaryFormLibrary)
    (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (H : System (N + 1)) (A : Point → Point) (V : Configuration (N + 1) → ℝ) (b E : ℝ)
    (hH : Facts (N + 1) H A V b) (ψ : State (N + 1)) (hψ : GroundState (N + 1) H E ψ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ)
    (hp : ∀ i k, MemLp (p i k) 2)
    (hw : WeakMomentum (N + 1) A (ψ : FullState (N + 1)) p) :
    ∃ U : PhaseUnitary (N + 1) η,
      Facts (N + 1) (gaugeOperator (N + 1) U.map H) (A + gradient η) V b ∧
      GroundState (N + 1) (gaugeOperator (N + 1) U.map H) E (U.map ψ) ∧
      (∀ i k, MemLp (wave (N + 1) η (p i k)) 2) ∧
      WeakMomentum (N + 1) (A + gradient η) (wave (N + 1) η (ψ : FullState (N + 1)))
        (fun i k => wave (N + 1) η (p i k)) ∧
      density N (wave (N + 1) η (ψ : FullState (N + 1))) = density N (ψ : FullState (N + 1)) ∧
      weakCurrent N (wave (N + 1) η (ψ : FullState (N + 1)))
        (fun i k => wave (N + 1) η (p i k)) = weakCurrent N (ψ : FullState (N + 1)) p := by
  obtain ⟨U, hU, hs, hm⟩ := gauge_realization multipliers transport (N + 1) η hη H A V b hH
  have hg : GroundState (N + 1) (gaugeOperator (N + 1) U.map H) E (U.map ψ) := by
    refine ⟨gauge_eigen (N + 1) U.map H E ψ hψ.1, ?_, ?_⟩
    · simpa only [hs] using hψ.2.1
    · simpa only [hm] using hψ.2.2
  exact ⟨U, hU, hg, fun i k => wave_memLp _ η hη _ (hp i k),
    weakMomentum_gauge _ η hη A _ p hw, density_gauge _ η _, weakCurrent_gauge _ η _ p⟩

end MagHK.GeneralGauge
