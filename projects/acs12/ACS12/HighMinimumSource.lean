import ACS12.HighMinimumActual
import ACS12.PressureGlobalFloor

/-! The complete minimum pressure upper at an original physical minimum mass. -/
namespace ACS12.Pressure

open Set MeasureTheory CenteredCircle.AllN
open GammaMeasure

theorem high_original_minimum_pressure_le {n : ℕ} {p t : ℝ} (hn : 3 ≤ n) (hp : 2 ≤ p)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (i : Fin n) (hMin : ∀ j, C.source.mass i ≤ C.source.mass j) (ht : 0 < t)
    (hT : imagePotential p C.source.period t =
      (F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)) / (2 * C.source.mass i)) :
    let S := C.source
    let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
    pressureAt p S i ≤ c / 2 * max 1 (highMinimumUnitPrice p (S.mass i / t)) + (highSelfCoefficient p / 2) * S.mass i * imageSelf p S.period := by
  let S := C.source
  let L := S.period
  let c := F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2)
  let d := S.forwardDistance i
  let e (j : Fin n) := S.forwardDistance j i
  let k := imagePotential p L
  let U := imageSlope p L
  let a := S.mass i
  have hn₂ : 2 ≤ n := by omega
  have hp₀ := (by linarith only [hp] : 0 < p)
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
  · exact high_minimumRay_pressure_le hp hL ht S.mass d e S.mass_pos hd he hl
      (S.forwardDistance_self i) hMin hPeriod hRatB.le
      (S.forwardDistance_caps C.circular_caps hl).1 h hT hU hCapsB
  · change pressureAt p C.source i ≤ _
    rw [pressureThroughSite_all hp₀ F C i]
    have hBound := high_minimumRay_pressure_le hp hL ht S.mass e d S.mass_pos he hd hj
      (S.forwardDistance_self i) hMin hPeriod hRatF.le
      (S.forwardDistance_caps C.circular_caps hj.symm).2 (by linarith only [hR,h]) hT hU.symm hCapsF
    unfold pressureBefore
    convert hBound using 1
    congr 1
    funext s
    dsimp only [leftRay,rightRay,S,d,e,L]
    ring

end ACS12.Pressure
