import MagHK.CoordinateLaplacian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic

/-! Cartesian expansion of the actual squared covariant derivative. -/
noncomputable section
namespace MagHK.CoordinateMagnetic
open scoped ContDiff BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def directional (basis : Fin 3 → X) (f : X → ℂ) (i : Fin 3) (x : X) : ℂ :=
  fderiv ℝ f x (basis i)

def momentum (basis : Fin 3 → X) (a : Fin 3 → X → ℝ) (f : X → ℂ)
    (i : Fin 3) (x : X) : ℂ :=
  -Complex.I * directional basis f i x + (a i x : ℂ) * f x

def magneticSquare (basis : Fin 3 → X) (a : Fin 3 → X → ℝ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ i : Fin 3, momentum basis a (momentum basis a f i) i x

theorem momentum_derivative (basis : Fin 3 → X) (a : Fin 3 → X → ℝ)
    (f : X → ℂ) (x : X) (hf : ContDiffAt ℝ 2 f x)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (i : Fin 3) :
    directional basis (momentum basis a f i) i x =
      -Complex.I * fderiv ℝ (fderiv ℝ f) x (basis i) (basis i) +
        (fderiv ℝ (a i) x (basis i) : ℂ) * f x +
        (a i x : ℂ) * directional basis f i x := by
  have hfd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpart := hfd.hasFDerivAt.clm_apply (hasFDerivAt_const (basis i) x)
  have hreal := Complex.ofRealCLM.hasFDerivAt.comp x (ha i).hasFDerivAt
  have hm := (hpart.const_mul (-Complex.I)).add
    (hreal.mul (hf.differentiableAt (by norm_num)).hasFDerivAt)
  have he := congrArg (fun L : X →L[ℝ] ℂ => L (basis i)) hm.fderiv
  change directional basis (momentum basis a f i) i x = _ at he
  convert he using 1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.flip_apply, map_zero, Function.comp_apply,
    smul_eq_mul, zero_add, add_zero, mul_zero, zero_mul,
    Complex.ofRealCLM_apply, directional]
  ring

theorem momentum_square_component (basis : Fin 3 → X) (a : Fin 3 → X → ℝ)
    (f : X → ℂ) (x : X) (hf : ContDiffAt ℝ 2 f x)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (i : Fin 3) :
    momentum basis a (momentum basis a f i) i x =
      -fderiv ℝ (fderiv ℝ f) x (basis i) (basis i) -
      2 * Complex.I * ((a i x : ℂ) * directional basis f i x) -
      Complex.I * (fderiv ℝ (a i) x (basis i) : ℂ) * f x +
      (a i x : ℂ) ^ 2 * f x := by
  change -Complex.I * directional basis (momentum basis a f i) i x +
    (a i x : ℂ) * momentum basis a f i x = _
  rw [momentum_derivative basis a f x hf ha i]
  simp only [momentum]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The universal Cartesian identity, with actual Frechet derivatives of
both the wavefunction and the real vector-potential components. -/
theorem magnetic_square_expansion (basis : Fin 3 → X) (a : Fin 3 → X → ℝ)
    (f : X → ℂ) (x : X) (hf : ContDiffAt ℝ 2 f x)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) :
    magneticSquare basis a f x =
      -MagHK.CoordinateLaplacian.laplacian basis f x -
      2 * Complex.I * (∑ i : Fin 3, (a i x : ℂ) * directional basis f i x) -
      Complex.I * (∑ i : Fin 3, (fderiv ℝ (a i) x (basis i) : ℂ)) * f x +
      (∑ i : Fin 3, (a i x : ℂ) ^ 2) * f x := by
  unfold magneticSquare
  simp_rw [momentum_square_component basis a f x hf ha]
  simp only [MagHK.CoordinateLaplacian.laplacian, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

end MagHK.CoordinateMagnetic
