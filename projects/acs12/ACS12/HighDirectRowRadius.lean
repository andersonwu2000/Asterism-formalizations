import ACS12.HighMinimumJensen

/-! The complete original row moment earns the seed-free radius inequality used in the direct HIGH floor. -/
namespace ACS12.Configuration
open Finset Pressure
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {p : ℝ} (F : ACS12.Configuration n p)

theorem radialUnitSource_row_moment_radius (hn : 2 ≤ n) (hp : 0 < p) (o i : Fin n) :
    let G := F.radialUnitSource hn o
    let M := massTotal G.mass
    2*(1/(2*G.radius)^2) ≤ M/(M-G.mass i)^(1+2/p) := by
  let G := F.radialUnitSource hn o
  let M := massTotal G.mass
  let T := M-G.mass i
  let D := 2*G.radius
  have hM : 0 < M := massTotal_pos (by omega) G.mass_pos
  have hT : 0 < T := sub_pos.mpr (massTotal_gt_mass hn G.mass_pos i)
  have hD : 0 < D := mul_pos zero_lt_two G.radius_pos
  have hJ := F.radialUnitSource_minimum_Jensen hn hp o i
  change T*(2*T/M)^(p/2) ≤ D^p at hJ
  have hBase : 0 < 2*T/M := by positivity
  have hPower := Real.rpow_le_rpow (mul_pos hT (Real.rpow_pos_of_pos hBase _)).le hJ
    (div_pos zero_lt_two hp).le
  rw [Real.mul_rpow hT.le (Real.rpow_pos_of_pos hBase _).le,
    ← Real.rpow_mul hBase.le,show (p/2)*(2/p) = (1:ℝ) by field_simp [hp.ne'],
    Real.rpow_one,← Real.rpow_mul hD.le,show p*(2/p) = (2:ℝ) by field_simp [hp.ne'],
    Real.rpow_two] at hPower
  have hFactor : T^(2/p)*(2*T/M) = 2*T^(1+2/p)/M := by
    rw [Real.rpow_add hT,Real.rpow_one]
    ring
  rw [hFactor] at hPower
  have hPaid := (div_le_iff₀ hM).mp hPower
  change 2*(1/D^2) ≤ M/T^(1+2/p)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT _)).mpr
  have hId : 2*(1/D^2)*T^(1+2/p) = (2*T^(1+2/p))/D^2 := by ring
  rw [hId]
  apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
  nlinarith only [hPaid]

theorem radialUnitSource_bad_row_moment_radius (hn : 2 ≤ n) (hp : 0 < p) (o i : Fin n)
    (hSmall : (F.radialUnitSource hn o).mass i ≤ 2/5) :
    let G := F.radialUnitSource hn o
    let U := massTotal G.mass-1
    2*(1/(2*G.radius)^2) ≤ (U+1)/(U+3/5)^(1+2/p) := by
  let G := F.radialUnitSource hn o
  let M := massTotal G.mass
  have hM := F.radialUnitSource_totalMass_ge_two hn o
  have hBase : 0 < M-2/5 := by change 2 ≤ M at hM; linarith only [hM]
  have hT : M-2/5 ≤ M-G.mass i := by linarith only [hSmall]
  have hPow := Real.rpow_le_rpow hBase.le hT (show 0 ≤ 1+2/p by positivity)
  have h := F.radialUnitSource_row_moment_radius hn hp o i
  change 2*(1/(2*G.radius)^2) ≤ M/(M-G.mass i)^(1+2/p) at h
  have hPrice := div_le_div_of_nonneg_left
    (show 0 ≤ M from (massTotal_pos (by omega) G.mass_pos).le)
    (Real.rpow_pos_of_pos hBase _) hPow
  have hEq : M-1+3/5 = M-2/5 := by ring
  change 2*(1/(2*G.radius)^2) ≤ (M-1+1)/(M-1+3/5)^(1+2/p)
  rw [hEq]
  norm_num only [sub_add_cancel]
  exact h.trans hPrice

end ACS12.Configuration
