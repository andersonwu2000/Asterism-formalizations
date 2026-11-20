import ACS12.PressureMaximumRadial
import ACS12.PressureMinimumActual
import ACS12.PressureFloor13
import ACS12.AdjacentRatios

/-! The original global mass floor on the closed pressure band. -/
namespace ACS12.Pressure

open Set MeasureTheory CenteredCircle.AllN
open GammaMeasure (imagePotential imagePotential_pos imageSlope imageSelf imageSelf_pos)

private theorem massPotential_le_unit {p L Q : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (hQ : 1 ≤ Q) : Q * imagePotential p L Q ≤ imagePotential p L 1 := by
  have hQ₀ := zero_lt_one.trans_le hQ
  have hK := imagePotential_pos (zero_lt_one.trans_le hp) hL zero_lt_one
  have h := imagePotential_scaled_upper hp hp₂ hL zero_lt_one hQ
  rw [one_div,Real.inv_rpow hQ₀.le,← Real.rpow_neg hQ₀.le] at h
  have hP : Q * Q ^ (-p) ≤ 1 := by
    rw [mul_comm,← Real.rpow_add_one hQ₀.ne']
    exact (Real.rpow_le_rpow_of_exponent_le hQ (show -p + 1 ≤ 0 by linarith only [hp])).trans_eq (Real.rpow_zero Q)
  calc
    _ ≤ Q * (Q ^ (-p) * imagePotential p L 1) := mul_le_mul_of_nonneg_left h hQ₀.le
    _ = (Q * Q ^ (-p)) * imagePotential p L 1 := by ring
    _ ≤ _ := mul_le_of_le_one_left hK.le hP

private theorem inverseMinimum_reciprocal {p L a Q t R C : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    (hL : 0 < L) (ha : 0 < a) (hQ : 0 < Q) (ht : 0 < t) (hQsmall : a / Q ≤ 1 / 13)
    (hC : Q * imagePotential p L Q < C) (hT : imagePotential p L t = C / (2 * a))
    (hR : C ≤ R * (Q * imagePotential p L Q)) :
    (a / t) ^ p ≤ (a / Q) ^ (p - 1) * R / 2 := by
  let k := imagePotential p L
  have hK := imagePotential_pos (zero_lt_one.trans_le hp) hL hQ
  change k t = C / (2 * a) at hT
  change 0 < k Q at hK
  change Q * k Q < C at hC
  change C ≤ R * (Q * k Q) at hR
  have haQ := (div_le_iff₀ hQ).mp hQsmall
  have hQT : k Q < k t := by
    rw [hT]
    apply (lt_div_iff₀ (mul_pos (by norm_num) ha)).mpr
    rw [mul_comm (k Q)]
    exact (mul_lt_mul_of_pos_right (show 2 * a < Q by linarith only [haQ,hQ]) hK).trans hC
  have htQ : t ≤ Q := by
    by_contra! h
    exact (imagePotential_strictAnti hp hp₂ hL hQ ht h).not_ge hQT.le
  have h := imagePotential_scaled_upper hp hp₂ hL ht htQ
  change k Q ≤ (t / Q) ^ p * k t at h
  rw [hT] at h
  have hD : 0 < t / Q := div_pos ht hQ
  have hP := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) ha)).mp
    (show k Q ≤ ((t / Q) ^ p * C) / (2 * a) by simpa only [mul_div_assoc] using h)
  have hR' := mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hD.le p)
  have hPay : 2 * a ≤ (t / Q) ^ p * (R * Q) := by
    apply (mul_le_mul_iff_left₀ hK).mp
    linarith only [hP,hR']
  have hA : (a / t) ^ p = (a / Q) ^ p / (t / Q) ^ p := by
    rw [← Real.div_rpow (div_nonneg ha.le hQ.le) hD.le]
    congr 1
    field_simp [ht.ne',hQ.ne']
  rw [hA]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hD _)).mpr
  rw [Real.rpow_sub_one (div_pos ha hQ).ne']
  have hMul := mul_le_mul_of_nonneg_left hPay (show 0 ≤ (a / Q) ^ p / (2 * a) by positivity)
  convert hMul using 1 <;> field_simp [ha.ne',hQ.ne'] <;> ring

theorem opposite_ray_bound {r g s Y : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : Y ≤ pressureBose r s) :
    Real.exp (-s * g) * (Y + r) ≤ oppositeRayBose r g s := by
  have hE : Real.exp (-s * g) * (pressureBose r s + r) = oppositeRayBose r g s := by
    rw [add_comm (pressureBose r s),mass_add_bose hr hs]
    unfold oppositeRayBose pressureBose
    have hExp : Real.exp (-(g - r) * s) * Real.exp (-s * r) = Real.exp (-s * g) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = r * Real.exp (-s * g) / periodicDen r s := by ring
      _ = _ := by rw [← hExp]; ring
  exact (mul_le_mul_of_nonneg_left (add_le_add_left h r) (Real.exp_pos _).le).trans_eq hE

theorem original_minimum_pressure_le {n : ℕ} {p t : ℝ} (hn : 3 ≤ n) (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (i : Fin n) (hMin : ∀ j, C.source.mass i ≤ C.source.mass j) (ht : 0 < t)
    (hT : imagePotential p C.source.period t =
      (F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)) / (2 * C.source.mass i)) :
    let S := C.source
    let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
    ∃ u ≥ 1, u ^ 3 ≤ 3 ∧
      pressureAt p S i ≤ c / 2 * max 1 (pressureNeighbor p u (S.mass i / t)) + S.mass i * imageSelf p S.period := by
  let S := C.source
  let L := S.period
  let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
  let d := S.forwardDistance i
  let e (j : Fin n) := S.forwardDistance j i
  let k := imagePotential p L
  let U := imageSlope p L
  let a := S.mass i
  have hn₂ : 2 ≤ n := by omega
  have hp₀ : 0 < p := by linarith only [hp]
  have hL := S.period_pos
  have ha := S.mass_pos i
  have hd := S.forwardDistance_pos i
  have he (j : Fin n) : 0 < e j := S.forwardDistance_pos j i
  obtain ⟨hR,hU⟩ := original_nonself_rows hp₀ F C i
  change nonselfRayRow L S.mass d i k + nonselfRayRow L S.mass e i k = c at hR
  change nonselfRayRow L S.mass d i U = nonselfRayRow L S.mass e i U at hU
  obtain ⟨j,hj,hjMin⟩ := exists_cyclic_nearest hn₂ S.forwardDistance i
  obtain ⟨l,hl,hlMin⟩ := exists_cyclic_nearest hn₂ (fun i j => S.forwardDistance j i) i
  have hPeriod : 2 * a ≤ L := by
    have h₁ := (S.forwardDistance_caps C.circular_caps hj.symm).1
    have h₂ := (S.forwardDistance_caps C.circular_caps hj).2
    rw [S.forwardDistance_flip hj.symm] at h₂
    linarith only [h₁,h₂]
  have hRatF := (F.adjacent_mass_ratios_lt (by omega) hp₀ C hj.symm (fun k hki hkj =>
    lt_of_le_of_ne (hjMin k hki) ((S.forwardDistance_injective i).ne hkj.symm))).2
  have hRatB := (F.adjacent_mass_ratios_lt (by omega) hp₀ C hl (fun k hkl hki => by
    have hSplit := cyclic_backward_split S i l hl hlMin k hkl
    have hLk := S.forwardDistance_lt_period hki
    have hFlip := S.forwardDistance_flip hkl
    linarith only [hSplit,hLk,hFlip])).1
  have hCapsF (s : ℝ) (hs : 0 < s) :
      rightRay S i s ≤ pressureBose a s ∧ rightRay S i s ≤ oppositeRayBose (S.mass j) (d j) s := by
    have hSh := rayWeight_shift hL hs S.mass (S.forwardDistance j) d j (S.forwardDistance_self j) rfl
      (cyclic_forward_split S i j hj hjMin)
    exact ⟨(occupied_rays_le_bose hn₂ S C.circular_caps i hs).2,by
      change rayWeight L S.mass d s ≤ _
      rw [hSh]
      exact opposite_ray_bound (S.mass_pos j) hs (occupied_rays_le_bose hn₂ S C.circular_caps j hs).2⟩
  have hCapsB (s : ℝ) (hs : 0 < s) :
      leftRay S i s ≤ pressureBose a s ∧ leftRay S i s ≤ oppositeRayBose (S.mass l) (e l) s := by
    have hSh := rayWeight_shift hL hs S.mass (fun k => S.forwardDistance k l) e l
      (S.forwardDistance_self l) rfl (cyclic_backward_split S i l hl hlMin)
    exact ⟨(occupied_rays_le_bose hn₂ S C.circular_caps i hs).1,by
      change rayWeight L S.mass e s ≤ _
      rw [hSh]
      exact opposite_ray_bound (S.mass_pos l) hs (occupied_rays_le_bose hn₂ S C.circular_caps l hs).1⟩
  rcases le_or_gt (nonselfRayRow L S.mass d i k) (c / 2) with h | h
  · obtain ⟨u,hu,huE,hB⟩ := minimumRay_pressure_le hp hp₂ hL ht S.mass d e S.mass_pos hd he hl
      (S.forwardDistance_self i) hMin hPeriod (S.forwardDistance_caps C.circular_caps hl).1 h hT hU hCapsB
    exact ⟨u,hu,huE.trans_le (hRatB.le.trans (by linarith only [hp₂])),hB⟩
  · obtain ⟨u,hu,huE,hBound⟩ := minimumRay_pressure_le hp hp₂ hL ht S.mass e d S.mass_pos he hd hj
      (S.forwardDistance_self i) hMin hPeriod (S.forwardDistance_caps C.circular_caps hj.symm).2
      (by linarith only [hR,h]) hT hU.symm hCapsF
    refine ⟨u,hu,huE.trans_le (hRatF.le.trans (by linarith only [hp₂])),?_⟩
    change pressureAt p C.source i ≤ _
    rw [pressureThroughSite hp₀ hp₂ F C i]
    unfold pressureBefore
    convert hBound using 1
    congr 1
    funext s
    dsimp only [leftRay,rightRay,S,d,e,L]
    ring

theorem original_mass_floor {n : ℕ} {p : ℝ} (hn : 3 ≤ n) (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (i j : Fin n) : C.source.mass j / 13 < C.source.mass i := by
  let S := C.source
  let L := S.period
  let k := imagePotential p L
  let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
  let self := imageSelf p L
  have hn₂ : 2 ≤ n := by omega
  have hp₁ : 1 < p := by linarith only [hp]
  have hp₀ := zero_lt_one.trans hp₁
  have hp₇ : 7 / 4 ≤ p := by linarith only [hp]
  have hL := S.period_pos
  obtain ⟨imax,_,hMax⟩ := Finset.univ.exists_max_image S.mass
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨i,Finset.mem_univ _⟩)
  obtain ⟨imin,_,hMin⟩ := Finset.univ.exists_min_image S.mass
    (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨i,Finset.mem_univ _⟩)
  let Q := S.mass imax
  let a := S.mass imin
  let D := Q * k Q
  let R := (c + Q * self) / D
  let P := pressureAt p S imin
  have hQ := S.mass_pos imax
  have ha := S.mass_pos imin
  have hQ₁ : 1 ≤ Q := by rw [← S.mass_root]; exact hMax S.root (Finset.mem_univ _)
  have hD : 0 < D := mul_pos hQ (imagePotential_pos hp₀ hL hQ)
  have hS : 0 < self := imageSelf_pos hp₀ hL
  have hC : D < c := (massPotential_le_unit hp₁.le hp₂ hL hQ₁).trans_lt (chartLevel_gt_potential_one hp₀ F C)
  have hR : 1 < R := (one_lt_div hD).mpr (hC.trans (lt_add_of_pos_right c (mul_pos hQ hS)))
  have hR₄ : R < 4 := by
    apply (div_lt_iff₀ hD).mpr
    have hB := original_maximum_radial_bound hn₂ hp₁ hp₂ F C imax (fun k => hMax k (Finset.mem_univ _))
    change c + Q * self ≤ 2 * D * GammaMeasure.powerTail p 1 at hB
    have h := mul_lt_mul_of_pos_left (pressure_zeta_lt_two hp₇) (show 0 < 2 * D by positivity)
    linarith only [hB,h]
  have hUnit := pressure_unit_normalized_gt hp hp₂ F C hQ₁
  change (7 / 5 : ℝ) * D < pressureAt p C.source S.root at hUnit
  rw [pressure_constant hp₀ hp₂ F C S.root imin] at hUnit
  change (7 / 5 : ℝ) * D < P at hUnit
  have hMaxP := pressure_maximum_gt hn₂ hp₀ F C C.circular_caps imax (fun k => hMax k (Finset.mem_univ _))
  change c + Q * self - maximumDebit p L Q < pressureAt p C.source imax at hMaxP
  rw [pressure_constant hp₀ hp₂ F C imax imin] at hMaxP
  have hMaxD := maximumDebit_le_boseDebit hp₁ hp₂ hL hQ
  have hMaxP' : (R - 23 / 20) * D < P := by
    have hD' := mul_lt_mul_of_pos_left (pressure_boseDebit_lt_twentyThirds hp) hD
    have hRD : R * D = c + Q * self := div_mul_cancel₀ _ hD.ne'
    change c + Q * self - maximumDebit p L Q < P at hMaxP
    change maximumDebit p L Q ≤ D * boseDebit p at hMaxD
    nlinarith only [hD',hRD,hMaxP,hMaxD]
  have hA : Q / 13 < a := by
    by_contra! hBad
    have hQsmall : a / Q ≤ 1 / 13 := (div_le_iff₀ hQ).mpr (by linarith only [hBad])
    have hc : 0 < c := hD.trans hC
    obtain ⟨t,ht,htEq⟩ := exists_imagePotential_eq hp₁.le hp₂ hL (div_pos hc (by positivity : 0 < 2 * a))
    have hRD : R * D = c + Q * self := div_mul_cancel₀ _ hD.ne'
    have hCR : c ≤ R * D := by rw [hRD]; linarith only [mul_pos hQ hS]
    have hY := inverseMinimum_reciprocal hp₁.le hp₂ hL ha hQ ht hQsmall hC htEq hCR
    have hYR := pressure_floor13Reciprocal_bound hp (div_pos ha hQ) hQsmall hR.le
      (div_nonneg ha.le ht.le) hY
    obtain ⟨u,hu,hu₃,hMinP⟩ := original_minimum_pressure_le hn hp hp₂ F C imin
      (fun k => hMin k (Finset.mem_univ _)) ht htEq
    let V := max 1 (pressureNeighbor (9 / 5) u (floor13Reciprocal R))
    have hV : 1 ≤ V := le_max_left _ _
    have hCap : max 1 (pressureNeighbor p u (a / t)) ≤ V :=
      max_le_max le_rfl ((pressureNeighbor_anti hu (div_nonneg ha.le ht.le) hp).trans
        (pressureNeighbor_mono hu (div_nonneg ha.le ht.le) hYR))
    have hPay : P ≤ (R / 2 * V) * D := by
      have hB := mul_le_mul_of_nonneg_left hCap (show 0 ≤ c / 2 by positivity)
      have hA' : a ≤ Q * V / 2 := by
        have h := mul_le_mul_of_nonneg_left hV hQ.le
        linarith only [h,hBad,hQ]
      have hA'' := mul_le_mul_of_nonneg_right hA' hS.le
      change P ≤ c / 2 * max 1 (pressureNeighbor p u (a / t)) + a * self at hMinP
      nlinarith only [hMinP,hB,hA'',congrArg (fun x : ℝ => x * V / 2) hRD]
    have hFloor := mul_lt_mul_of_pos_right
      (pressureFloor13_branch_lt hu hu₃ (zero_lt_one.trans hR).le hR₄.le) hD
    rw [max_mul_of_nonneg _ _ hD.le] at hFloor
    have hStrict : max ((7 / 5 : ℝ) * D) ((R - 23 / 20) * D) < P := max_lt hUnit hMaxP'
    exact (hFloor.trans hStrict).not_ge hPay
  exact (div_le_div_of_nonneg_right (hMax j (Finset.mem_univ _)) (by norm_num)).trans_lt
    (hA.trans_le (hMin i (Finset.mem_univ _)))

end ACS12.Pressure
