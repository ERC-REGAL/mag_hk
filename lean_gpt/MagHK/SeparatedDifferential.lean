import MagHK.MonopoleRealization
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Direct differential calculation for a common radial doublet. Every
operator below is the literal radial and angular expression used in the
Friedrichs realization, not an abstract radial replacement. -/
noncomputable section
namespace MagHK.MonopoleSeparation
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleAngular MagHK.MonopoleTrial
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

theorem deriv_linear {s : Set ℝ} (hs : IsOpen s) (f g : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s)
    (a b : ℂ) (x : ℝ) (hx : x ∈ s) :
    deriv (fun y => a * f y + b * g y) x = a * deriv f x + b * deriv g x := by
  have hfd := (hf.differentiableOn (by decide) x hx).differentiableAt (hs.mem_nhds hx)
  have hgd := (hg.differentiableOn (by decide) x hx).differentiableAt (hs.mem_nhds hx)
  change deriv ((fun y => a * f y) + (fun y => b * g y)) x = _
  rw [deriv_add (hfd.const_mul a) (hgd.const_mul b),
    deriv_const_mul_field, deriv_const_mul_field]

theorem deriv_second_linear {s : Set ℝ} (hs : IsOpen s) (f g : ℝ → ℂ)
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s)
    (a b : ℂ) (x : ℝ) (hx : x ∈ s) :
    deriv (deriv (fun y => a * f y + b * g y)) x =
      a * deriv (deriv f) x + b * deriv (deriv g) x := by
  have he : deriv (fun y => a * f y + b * g y) =ᶠ[𝓝 x]
      (fun y => a * deriv f y + b * deriv g y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact deriv_linear hs f g hf hg a b y hy
  rw [he.deriv_eq]
  have hfd := ((hf.deriv_of_isOpen hs (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableOn
    (by norm_num) x hx).differentiableAt (hs.mem_nhds hx)
  have hgd := ((hg.deriv_of_isOpen hs (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableOn
    (by norm_num) x hx).differentiableAt (hs.mem_nhds hx)
  change deriv ((fun y => a * deriv f y) + (fun y => b * deriv g y)) x = _
  rw [deriv_add (hfd.const_mul a) (hgd.const_mul b),
    deriv_const_mul_field, deriv_const_mul_field]

theorem angular_linear (g : ℝ) (f h : Angle → ℂ)
    (hf : ContDiffOn ℝ 2 f (Ioo (-1 : ℝ) 1 ×ˢ univ))
    (hh : ContDiffOn ℝ 2 h (Ioo (-1 : ℝ) 1 ×ˢ univ))
    (a b : ℂ) (p : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    angularExpression g (fun x => a * f x + b * h x) p =
      a * angularExpression g f p + b * angularExpression g h p := by
  have fm : ContDiffOn ℝ 2 (fun μ => f (μ, p.2)) (Ioo (-1 : ℝ) 1) :=
    hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hm => ⟨hm, mem_univ _⟩)
  have hm : ContDiffOn ℝ 2 (fun μ => h (μ, p.2)) (Ioo (-1 : ℝ) 1) :=
    hh.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hm => ⟨hm, mem_univ _⟩)
  have fp : ContDiffOn ℝ 2 (fun φ => f (p.1, φ)) univ :=
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hp, mem_univ _⟩)
  have hp' : ContDiffOn ℝ 2 (fun φ => h (p.1, φ)) univ :=
    hh.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨hp, mem_univ _⟩)
  have dm := deriv_linear isOpen_Ioo _ _ fm hm a b p.1 hp
  have dp := deriv_linear isOpen_univ _ _ fp hp' a b p.2 (mem_univ _)
  have dmm := deriv_second_linear isOpen_Ioo _ _ fm hm a b p.1 hp
  have dpp := deriv_second_linear isOpen_univ _ _ fp hp' a b p.2 (mem_univ _)
  unfold angularExpression Dμ Dφ
  rw [dm, dp, dmm, dpp]
  ring

theorem angular_scale (g : ℝ) (f : Angle → ℂ) (a : ℂ) (p : Angle) :
    angularExpression g (fun x => a * f x) p = a * angularExpression g f p := by
  simp only [angularExpression, Dμ, Dφ, deriv_const_mul_field]
  ring

theorem angularDet_first (p q : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    angularExpression (1 / 2) (fun a => angularDet a q) p = (1 / 2 : ℂ) * angularDet p q := by
  have he : (fun a => angularDet a q) =
      (fun a => (MagHK.Slater.scale * Yminus q) * Yplus a +
        (-MagHK.Slater.scale * Yplus q) * Yminus a) := by
    funext a
    unfold angularDet MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
    ring
  rw [he, angular_linear _ _ _ Yplus_contDiffOn Yminus_contDiffOn _ _ p hp,
    Yplus_equation p hp, Yminus_equation p hp]
  unfold angularDet MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  ring

theorem angularDet_second (p q : Angle) (hq : q.1 ∈ Ioo (-1 : ℝ) 1) :
    angularExpression (1 / 2) (fun a => angularDet p a) q = (1 / 2 : ℂ) * angularDet p q := by
  have he : (fun a => angularDet p a) = fun a => (-1 : ℂ) * angularDet a p := by
    funext a
    rw [neg_one_mul]
    exact angularDet_antisymmetric p a
  rw [he, angular_scale, angularDet_first q p hq, angularDet_antisymmetric q p]
  ring

def radialExpression (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  -deriv (deriv f) r - (2 / r : ℝ) * deriv f r +
    ((1 / 2 / r ^ 2 + r ^ 2 : ℝ) : ℂ) * f r

def separatedWave (f : ℝ → ℂ) (p : Chart × Chart) : ℂ :=
  f p.1.1 * f p.2.1 * angularDet p.1.2 p.2.2

theorem separated_first (f : ℝ → ℂ) (p : Chart × Chart)
    (hp : p.1.2.1 ∈ Ioo (-1 : ℝ) 1) :
    oneExpression 1 (fun x => separatedWave f (x, p.2)) p.1 =
      radialExpression f p.1.1 * f p.2.1 * angularDet p.1.2 p.2.2 := by
  simp only [oneExpression, Dr, separatedWave, deriv_mul_const_field]
  have ha := angular_scale (1 / 2) (fun a => angularDet a p.2.2)
    (f p.1.1 * f p.2.1) p.1.2
  simp only [Int.cast_one]
  rw [ha, angularDet_first p.1.2 p.2.2 hp]
  simp only [radialExpression, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem separated_second (f : ℝ → ℂ) (p : Chart × Chart)
    (hp : p.2.2.1 ∈ Ioo (-1 : ℝ) 1) :
    oneExpression 1 (fun y => separatedWave f (p.1, y)) p.2 =
      f p.1.1 * radialExpression f p.2.1 * angularDet p.1.2 p.2.2 := by
  simp only [oneExpression, Dr, separatedWave, deriv_mul_const_field, deriv_const_mul_field]
  have ha := angular_scale (1 / 2) (fun a => angularDet p.1.2 a)
    (f p.1.1 * f p.2.1) p.2.2
  simp only [Int.cast_one]
  rw [ha, angularDet_second p.1.2 p.2.2 hp]
  simp only [radialExpression, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem separated_equation (f : ℝ → ℂ) (E : ℝ) (p : Chart × Chart)
    (hp : p.1.2.1 ∈ Ioo (-1 : ℝ) 1) (hq : p.2.2.1 ∈ Ioo (-1 : ℝ) 1)
    (he : pairExpression 1 coulomb (separatedWave f) p = (E : ℂ) * separatedWave f p) :
    (radialExpression f p.1.1 * f p.2.1 + f p.1.1 * radialExpression f p.2.1 +
      ((coulomb p : ℂ) - E) * (f p.1.1 * f p.2.1)) * angularDet p.1.2 p.2.2 = 0 := by
  rw [pairExpression, separated_first f p hp, separated_second f p hq] at he
  dsimp only [separatedWave] at he
  linear_combination he

end MagHK.MonopoleSeparation
