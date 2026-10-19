import MagHK.DiracString
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Literal Cartesian north and south connections, their smooth patch
extensions, common curvature, and local azimuthal gauge difference. -/
noncomputable section
namespace MagHK.MonopolePatches
open Set MagHK.ConstructionData
open scoped ContDiff
set_option maxHeartbeats 1000000
abbrev radius := MagHK.DiracString.radius

def northDomain : Set Space := {p | 0 < radius p + p.2}
def southDomain : Set Space := {p | 0 < radius p - p.2}
def coefficient (g : ℝ) (p : Space) : ℝ := g / (radius p * (radius p + p.2))
def north (g : ℝ) (p : Space) : Space := ((-p.1.2 * coefficient g p, p.1.1 * coefficient g p), 0)
def south (g : ℝ) (p : Space) : Space := north g (-p)
def field (g : ℝ) (p : Space) : Space := (g / radius p ^ 3) • p

def curl (A : Space → Space) (p : Space) : Space :=
  ((deriv (fun y => (A ((p.1.1, y), p.2)).2) p.1.2 -
      deriv (fun z => (A (p.1, z)).1.2) p.2,
    deriv (fun z => (A (p.1, z)).1.1) p.2 -
      deriv (fun x => (A ((x, p.1.2), p.2)).2) p.1.1),
    deriv (fun x => (A ((x, p.1.2), p.2)).1.2) p.1.1 -
      deriv (fun y => (A ((p.1.1, y), p.2)).1.1) p.1.2)

theorem radius_sq (p : Space) : radius p ^ 2 = p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem radius_neg (p : Space) : radius (-p) = radius p := by
  simp [MagHK.DiracString.radius]

theorem radius_pos (p : Space) (hp : p ≠ 0) : 0 < radius p := by
  apply Real.sqrt_pos.mpr
  have h : 0 ≤ p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 := by positivity
  by_contra hn
  have hz : p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = 0 := le_antisymm (le_of_not_gt hn) h
  apply hp
  ext <;> dsimp <;> nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2, sq_nonneg p.2]

theorem north_nonzero {p : Space} (hp : p ∈ northDomain) : p ≠ 0 := by
  rintro rfl
  simpa [northDomain, MagHK.DiracString.radius] using hp

theorem north_domain_iff (p : Space) : p ∈ northDomain ↔ p.1 ≠ 0 ∨ 0 < p.2 := by
  have hr : 0 ≤ radius p := Real.sqrt_nonneg _
  have hs := radius_sq p
  constructor
  · intro hp
    by_cases h : p.1 = 0
    · right
      have hx : p.1.1 = 0 := congrArg Prod.fst h
      have hy : p.1.2 = 0 := congrArg Prod.snd h
      change 0 < radius p + p.2 at hp
      rw [hx, hy] at hs
      nlinarith
    · exact Or.inl h
  · intro hp
    change 0 < radius p + p.2
    rcases hp with hp | hp
    · by_contra hn
      have hz : p.1.1 = 0 ∧ p.1.2 = 0 := by
        constructor <;> nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
      exact hp (Prod.ext hz.1 hz.2)
    · linarith

theorem south_domain_iff (p : Space) : p ∈ southDomain ↔ p.1 ≠ 0 ∨ p.2 < 0 := by
  have h := north_domain_iff (-p)
  simpa [northDomain, southDomain, radius_neg, sub_eq_add_neg] using h

theorem radius_contDiffAt (p : Space) (hp : p ≠ 0) : ContDiffAt ℝ ∞ radius p := by
  have hs : ContDiff ℝ ∞ (fun p : Space => p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2) := by fun_prop
  apply hs.contDiffAt.sqrt
  have hr := radius_pos p hp
  have he := radius_sq p
  nlinarith

theorem north_smooth (g : ℝ) : ContDiffOn ℝ ∞ (north g) northDomain := by
  intro p hp
  have hr := radius_contDiffAt p (north_nonzero hp)
  have hz : ContDiffAt ℝ ∞ (fun p : Space => p.2) p := by fun_prop
  have hc : ContDiffAt ℝ ∞ (coefficient g) p :=
    contDiffAt_const.div (hr.mul (hr.add hz))
      (mul_ne_zero (radius_pos p (north_nonzero hp)).ne' (ne_of_gt hp))
  exact (((by fun_prop : ContDiffAt ℝ ∞ (fun p : Space => -p.1.2) p).mul hc).prodMk
    ((by fun_prop : ContDiffAt ℝ ∞ (fun p : Space => p.1.1) p).mul hc)).prodMk
      contDiffAt_const |>.contDiffWithinAt

theorem south_smooth (g : ℝ) : ContDiffOn ℝ ∞ (south g) southDomain := by
  apply (north_smooth g).comp (contDiff_neg.contDiffOn)
  intro p hp
  simpa [northDomain, southDomain, radius_neg, sub_eq_add_neg] using hp

private theorem sqrt_line (a b : ℝ) (h : 0 < a ^ 2 + b) :
    HasDerivAt (fun t => Real.sqrt (t ^ 2 + b)) (a / Real.sqrt (a ^ 2 + b)) a := by
  convert (((hasDerivAt_id a).pow 2).add_const b).sqrt h.ne' using 1
  all_goals simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  all_goals first | (ext t <;> congr 1 <;> ring) | (field_simp <;> ring)

private theorem radius_dx (p : Space) (hp : p ≠ 0) :
    HasDerivAt (fun t => radius ((t, p.1.2), p.2)) (p.1.1 / radius p) p.1.1 := by
  have h := sqrt_line p.1.1 (p.1.2 ^ 2 + p.2 ^ 2)
    (by have := radius_pos p hp; have := radius_sq p; nlinarith)
  simpa [MagHK.DiracString.radius, add_assoc] using h

private theorem radius_dy (p : Space) (hp : p ≠ 0) :
    HasDerivAt (fun t => radius ((p.1.1, t), p.2)) (p.1.2 / radius p) p.1.2 := by
  have h := sqrt_line p.1.2 (p.1.1 ^ 2 + p.2 ^ 2)
    (by have := radius_pos p hp; have := radius_sq p; nlinarith)
  simpa [MagHK.DiracString.radius, add_comm, add_left_comm, add_assoc] using h

private theorem radius_dz (p : Space) (hp : p ≠ 0) :
    HasDerivAt (fun t => radius (p.1, t)) (p.2 / radius p) p.2 := by
  have h := sqrt_line p.2 (p.1.1 ^ 2 + p.1.2 ^ 2)
    (by have := radius_pos p hp; have := radius_sq p; nlinarith)
  simpa [MagHK.DiracString.radius, add_comm, add_left_comm, add_assoc] using h

private theorem coefficient_dx (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    HasDerivAt (fun t => coefficient g ((t, p.1.2), p.2))
      (-g * p.1.1 * (2 * radius p + p.2) / (radius p ^ 3 * (radius p + p.2) ^ 2)) p.1.1 := by
  have hr := radius_dx p (north_nonzero hp)
  have hd := (hasDerivAt_const p.1.1 g).div (hr.mul (hr.add_const p.2))
    (mul_ne_zero (radius_pos p (north_nonzero hp)).ne' (ne_of_gt hp))
  convert hd using 1 <;> try rfl
  all_goals simp only [coefficient, Pi.div_apply, Pi.mul_apply, Pi.add_apply, id_eq]
  all_goals field_simp [(radius_pos p (north_nonzero hp)).ne',
    (show radius p + p.2 ≠ 0 from ne_of_gt hp)] <;> ring

private theorem coefficient_dy (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    HasDerivAt (fun t => coefficient g ((p.1.1, t), p.2))
      (-g * p.1.2 * (2 * radius p + p.2) / (radius p ^ 3 * (radius p + p.2) ^ 2)) p.1.2 := by
  have hr := radius_dy p (north_nonzero hp)
  have hd := (hasDerivAt_const p.1.2 g).div (hr.mul (hr.add_const p.2))
    (mul_ne_zero (radius_pos p (north_nonzero hp)).ne' (ne_of_gt hp))
  convert hd using 1 <;> try rfl
  all_goals simp only [coefficient, Pi.div_apply, Pi.mul_apply, Pi.add_apply, id_eq]
  all_goals field_simp [(radius_pos p (north_nonzero hp)).ne',
    (show radius p + p.2 ≠ 0 from ne_of_gt hp)] <;> ring

private theorem coefficient_dz (g : ℝ) (p : Space) (hp : p ∈ northDomain) :
    HasDerivAt (fun t => coefficient g (p.1, t)) (-g / radius p ^ 3) p.2 := by
  have hr := radius_dz p (north_nonzero hp)
  have hd := (hasDerivAt_const p.2 g).div (hr.mul (hr.add (hasDerivAt_id p.2)))
    (mul_ne_zero (radius_pos p (north_nonzero hp)).ne' (ne_of_gt hp))
  convert hd using 1 <;> try rfl
  all_goals simp only [coefficient, Pi.div_apply, Pi.mul_apply, Pi.add_apply, id_eq]
  all_goals field_simp [(radius_pos p (north_nonzero hp)).ne',
    (show radius p + p.2 ≠ 0 from ne_of_gt hp)] <;> ring

theorem north_curl (g : ℝ) (p : Space) (hp : p ∈ northDomain) : curl (north g) p = field g p := by
  have hx := ((hasDerivAt_id p.1.1).mul (coefficient_dx g p hp)).deriv
  have hy := ((hasDerivAt_id p.1.2).neg.mul (coefficient_dy g p hp)).deriv
  have hzx := ((coefficient_dz g p hp).const_mul p.1.1).deriv
  have hzy := ((coefficient_dz g p hp).const_mul (-p.1.2)).deriv
  simp only [id_eq, one_mul, neg_one_mul] at hx hy
  change deriv (fun x => x * coefficient g ((x, p.1.2), p.2)) p.1.1 = _ at hx
  change deriv (fun y => -y * coefficient g ((p.1.1, y), p.2)) p.1.2 = _ at hy
  simp only [Pi.neg_apply, id_eq] at hy
  simp only [curl, north, deriv_const]
  change ((0 - deriv (fun z => p.1.1 * coefficient g (p.1, z)) p.2,
    deriv (fun z => -p.1.2 * coefficient g (p.1, z)) p.2 - 0),
    deriv (fun x => x * coefficient g ((x, p.1.2), p.2)) p.1.1 -
    deriv (fun y => -y * coefficient g ((p.1.1, y), p.2)) p.1.2) = _
  rw [hx, hy, hzx, hzy]
  have hr := (radius_pos p (north_nonzero hp)).ne'
  have hd : radius p + p.2 ≠ 0 := ne_of_gt hp
  have hs := radius_sq p
  ext <;> dsimp [field, coefficient]
  · ring
  · ring
  · field_simp [hr, hd]
    linear_combination g * (2 * radius p + p.2) * hs

theorem curl_comp_neg (A : Space → Space) (p : Space) :
    curl (fun x => A (-x)) p = -curl A (-p) := by
  simp only [curl]
  dsimp
  rw [deriv_comp_neg (fun y : ℝ => (A ((-p.1.1, y), -p.2)).2),
    deriv_comp_neg (fun z : ℝ => (A (-p.1, z)).1.2),
    deriv_comp_neg (fun z : ℝ => (A (-p.1, z)).1.1),
    deriv_comp_neg (fun x : ℝ => (A ((x, -p.1.2), -p.2)).2),
    deriv_comp_neg (fun x : ℝ => (A ((x, -p.1.2), -p.2)).1.2),
    deriv_comp_neg (fun y : ℝ => (A ((-p.1.1, y), -p.2)).1.1)]
  congr 2 <;> ring

theorem south_curl (g : ℝ) (p : Space) (hp : p ∈ southDomain) : curl (south g) p = field g p := by
  have hn : -p ∈ northDomain := by
    simpa [northDomain, southDomain, radius_neg, sub_eq_add_neg] using hp
  change curl (fun x => north g (-x)) p = _
  rw [curl_comp_neg, north_curl g (-p) hn]
  simp [field, radius_neg]

theorem north_eq_string (g : ℝ) (p : Space) (hxy : p.1 ≠ 0) :
    north g p = MagHK.DiracString.potential g p := by
  have hn : p ∈ northDomain := (north_domain_iff p).mpr (Or.inl hxy)
  have hr := (radius_pos p (north_nonzero hn)).ne'
  have hd : radius p + p.2 ≠ 0 := ne_of_gt hn
  have hs := radius_sq p
  have hq : p.1.1 ^ 2 + p.1.2 ^ 2 ≠ 0 := by
    intro h
    apply hxy
    ext <;> dsimp <;> nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
  have hc : coefficient g p = g * (1 - p.2 / radius p) / (p.1.1 ^ 2 + p.1.2 ^ 2) := by
    unfold coefficient
    field_simp [hr, hd, hq]
    linear_combination -g * hs
  simp [north, MagHK.DiracString.potential, hc]

def azimuthal (p : Space) : Space := ((-p.1.2 / (p.1.1 ^ 2 + p.1.2 ^ 2),
  p.1.1 / (p.1.1 ^ 2 + p.1.2 ^ 2)), 0)

theorem patch_difference (g : ℝ) (p : Space) (hxy : p.1 ≠ 0) :
    north g p - south g p = (2 * g) • azimuthal p := by
  rw [south, north_eq_string g p hxy, north_eq_string g (-p) (by simpa using hxy)]
  simp only [MagHK.DiracString.potential, radius_neg, azimuthal]
  dsimp
  simp only [neg_neg, neg_sq, smul_eq_mul]
  ext <;> dsimp <;> ring

end MagHK.MonopolePatches
