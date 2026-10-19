import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Actual Bochner integral identities for a two-orbital Slater determinant.
The only analytic hypotheses are integrability and the usual orthonormal
orbital integrals. The density and current conclusions are derived.
-/

noncomputable section
namespace MagHK.Slater
open MeasureTheory

variable {Y : Type*} [MeasurableSpace Y]

structure OrthonormalPair (μ : Measure Y) (f g : Y → ℂ) : Prop where
  integrable_ff : Integrable (fun y => star (f y) * f y) μ
  integrable_gg : Integrable (fun y => star (g y) * g y) μ
  integrable_fg : Integrable (fun y => star (f y) * g y) μ
  integrable_gf : Integrable (fun y => star (g y) * f y) μ
  norm_f : (∫ y, star (f y) * f y ∂μ) = 1
  norm_g : (∫ y, star (g y) * g y ∂μ) = 1
  orthogonal_fg : (∫ y, star (f y) * g y ∂μ) = 0
  orthogonal_gf : (∫ y, star (g y) * f y ∂μ) = 0

def determinantSlice (a b : ℂ) (f g : Y → ℂ) (y : Y) : ℂ :=
  a * g y - b * f y

def scale : ℂ := (Real.sqrt 2 : ℂ)⁻¹

def slaterSlice (a b : ℂ) (f g : Y → ℂ) (y : Y) : ℂ :=
  scale * determinantSlice a b f g y

theorem determinant_pairing_expansion (a b c d : ℂ) (f g : Y → ℂ) (y : Y) :
    star (determinantSlice a b f g y) * determinantSlice c d f g y =
      (star a * c) * (star (g y) * g y) +
      (star b * d) * (star (f y) * f y) -
      (star a * d) * (star (g y) * f y) -
      (star b * c) * (star (f y) * g y) := by
  simp only [determinantSlice, star_sub, star_mul]
  ring

theorem integrable_determinant_pairing (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) (a b c d : ℂ) :
    Integrable (fun y => star (determinantSlice a b f g y) *
      determinantSlice c d f g y) μ := by
  simp_rw [determinant_pairing_expansion]
  exact (((h.integrable_gg.const_mul (star a * c)).add
    (h.integrable_ff.const_mul (star b * d))).sub
    (h.integrable_gf.const_mul (star a * d))).sub
    (h.integrable_fg.const_mul (star b * c))

theorem integral_determinant_pairing (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) (a b c d : ℂ) :
    (∫ y, star (determinantSlice a b f g y) *
      determinantSlice c d f g y ∂μ) = star a * c + star b * d := by
  simp_rw [determinant_pairing_expansion]
  rw [integral_sub (f := fun y =>
        (star a * c) * (star (g y) * g y) +
        (star b * d) * (star (f y) * f y) -
        (star a * d) * (star (g y) * f y))
      (((h.integrable_gg.const_mul (star a * c)).add
        (h.integrable_ff.const_mul (star b * d))).sub
        (h.integrable_gf.const_mul (star a * d)))
      (h.integrable_fg.const_mul (star b * c)),
    integral_sub (f := fun y =>
        (star a * c) * (star (g y) * g y) +
        (star b * d) * (star (f y) * f y))
      ((h.integrable_gg.const_mul (star a * c)).add
        (h.integrable_ff.const_mul (star b * d)))
      (h.integrable_gf.const_mul (star a * d)),
    integral_add (h.integrable_gg.const_mul (star a * c))
      (h.integrable_ff.const_mul (star b * d))]
  simp only [integral_const_mul, h.norm_f, h.norm_g,
    h.orthogonal_fg, h.orthogonal_gf, mul_one, mul_zero, sub_zero]

theorem scale_normalization : (2 : ℂ) * star scale * scale = 1 := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsc : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by exact_mod_cast hs
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  simp only [scale, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  field_simp
  exact hsc.symm

theorem slater_pairing_pointwise (a b c d : ℂ) (f g : Y → ℂ) (y : Y) :
    (2 : ℂ) * (star (slaterSlice a b f g y) * slaterSlice c d f g y) =
      star (determinantSlice a b f g y) * determinantSlice c d f g y := by
  simp only [slaterSlice, star_mul]
  calc
    2 * (star (determinantSlice a b f g y) * star scale *
        (scale * determinantSlice c d f g y)) =
      (2 * star scale * scale) *
        (star (determinantSlice a b f g y) * determinantSlice c d f g y) := by ring
    _ = _ := by rw [scale_normalization, one_mul]

theorem integrable_slater_pairing (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) (a b c d : ℂ) :
    Integrable (fun y => star (slaterSlice a b f g y) *
      slaterSlice c d f g y) μ := by
  have hp : (fun y => star (slaterSlice a b f g y) * slaterSlice c d f g y) =
      (fun y => (star scale * scale) *
        (star (determinantSlice a b f g y) * determinantSlice c d f g y)) := by
    funext y
    simp only [slaterSlice, star_mul]
    ring
  rw [hp]
  exact (integrable_determinant_pairing μ f g h a b c d).const_mul _

theorem slater_transition_marginal (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) (a b c d : ℂ) :
    (2 : ℂ) * (∫ y, star (slaterSlice a b f g y) *
      slaterSlice c d f g y ∂μ) = star a * c + star b * d := by
  rw [← integral_const_mul]
  simp_rw [slater_pairing_pointwise]
  exact integral_determinant_pairing μ f g h a b c d

/-- Normalization of the determinant, expressed as its iterated norm
integral. Tonelli identifies this with the product-space L² norm. -/
theorem slater_iterated_normalization (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) :
    (∫ x, ∫ y, Complex.normSq (slaterSlice (f x) (g x) f g y) ∂μ ∂μ) = 1 := by
  have hi : (2 : ℂ) * (∫ x, ∫ y,
        star (slaterSlice (f x) (g x) f g y) *
          slaterSlice (f x) (g x) f g y ∂μ ∂μ) = 2 := by
    rw [← integral_const_mul]
    simp_rw [slater_transition_marginal μ f g h]
    rw [integral_add h.integrable_ff h.integrable_gg, h.norm_f, h.norm_g]
    norm_num
  have hn : (∫ x, ∫ y,
        star (slaterSlice (f x) (g x) f g y) *
          slaterSlice (f x) (g x) f g y ∂μ ∂μ) = (1 : ℂ) := by
    apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
    simpa using hi
  simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    integral_complex_ofReal] at hn
  exact_mod_cast hn

theorem slater_density_marginal (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) (a b : ℂ) :
    2 * (∫ y, Complex.normSq (slaterSlice a b f g y) ∂μ) =
      Complex.normSq a + Complex.normSq b := by
  have he := slater_transition_marginal μ f g h a b a b
  have hi := integral_re (integrable_slater_pairing μ f g h a b a b)
  change (∫ y, (star (slaterSlice a b f g y) * slaterSlice a b f g y).re ∂μ) =
    (∫ y, star (slaterSlice a b f g y) * slaterSlice a b f g y ∂μ).re at hi
  have hr (z : ℂ) : (star z * z).re = Complex.normSq z := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rfl
  have he' := congrArg Complex.re he
  have hm (z : ℂ) : ((2 : ℂ) * z).re = 2 * z.re := by simp [Complex.mul_re]
  rw [hm, Complex.add_re] at he'
  rw [← hi] at he'
  simp_rw [hr] at he'
  exact he'

/-- One Cartesian component of the current. Here `c` and `d` are the
corresponding derivatives of the two orbitals at the observation point.
The same identity applies independently to each component. -/
theorem slater_current_marginal (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) (a b c d : ℂ) :
    2 * (∫ y, (star (slaterSlice a b f g y) *
      slaterSlice c d f g y).im ∂μ) =
      (star a * c).im + (star b * d).im := by
  have he := congrArg Complex.im (slater_transition_marginal μ f g h a b c d)
  have hi := integral_im (integrable_slater_pairing μ f g h a b c d)
  change (∫ y, (star (slaterSlice a b f g y) * slaterSlice c d f g y).im ∂μ) =
    (∫ y, star (slaterSlice a b f g y) * slaterSlice c d f g y ∂μ).im at hi
  have hm (z : ℂ) : ((2 : ℂ) * z).im = 2 * z.im := by simp [Complex.mul_im]
  rw [hm, Complex.add_im] at he
  rw [← hi] at he
  exact he

theorem slater_physical_current_marginal (μ : Measure Y) (f g : Y → ℂ)
    (h : OrthonormalPair μ f g) (a b c d : ℂ) (A : ℝ) :
    2 * (∫ y, (star (slaterSlice a b f g y) *
      slaterSlice c d f g y).im ∂μ) +
        (2 * ∫ y, Complex.normSq (slaterSlice a b f g y) ∂μ) * A =
      ((star a * c).im + Complex.normSq a * A) +
        ((star b * d).im + Complex.normSq b * A) := by
  rw [slater_current_marginal μ f g h a b c d, slater_density_marginal μ f g h a b]
  ring

theorem slater_antisymmetry (f g : Y → ℂ) (x y : Y) :
    slaterSlice (f x) (g x) f g y = -slaterSlice (f y) (g y) f g x := by
  unfold slaterSlice determinantSlice
  ring

/-- Differentiation in the observation coordinate gives exactly the second
Slater slice used in the current theorem. -/
theorem slater_hasDerivAt (f g : ℝ → ℂ) (x y : ℝ) (df dg : ℂ)
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun z => slaterSlice (f z) (g z) f g y)
      (slaterSlice df dg f g y) x := by
  have hd : HasDerivAt (fun z => f z * g y - g z * f y)
      (df * g y - dg * f y) x :=
    (hf.mul_const (g y)).sub (hg.mul_const (f y))
  simpa only [slaterSlice, determinantSlice] using hd.const_mul scale

end MagHK.Slater
