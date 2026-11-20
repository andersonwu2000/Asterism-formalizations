import ACS12.PressureGeneralStress

/-! Integrate the full pressure across each original cut, with the period and self rays retained. -/
namespace ACS12.Pressure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaMeasure (imageDensity imageSlopeIntegrand imageSlopeIntegral imageSlopeTail_integrable)

theorem stressKernel_integrable {p L D t : ℝ} (hp : 0 < p) (_hp₂ : p ≤ 2) (hL : 0 < L) (hD : 0 < D) (ht : 0 < t) :
    IntegrableOn (fun s => imageDensity p L s * s * Real.exp (-s * t) / (periodicDen D s) ^ 2) (Ioi 0) :=
  stressKernel_integrable_all hp hL hD ht

noncomputable def pressureWeight (p L s : ℝ) : ℝ := imageDensity p L s * s

theorem ray_integrable {n : ℕ} {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (m d : Fin n → ℝ) (hd : ∀ j, 0 < d j) :
    IntegrableOn (fun s => pressureWeight p L s * rayWeight L m d s) (Ioi 0) := by
  have hI (j : Fin n) := (imageSlopeTail_integrable hp hL (hd j)).const_mul (m j)
  refine (integrable_finsetSum Finset.univ (fun j _ => hI j)).congr ?_
  exact Eventually.of_forall fun s => by
    dsimp only [pressureWeight,rayWeight,periodicDen]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem rays_product_integrable_all {n : ℕ} {p L : ℝ} (hp : 0 < p) (hL : 0 < L)
    (m a b : Fin n → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) :
    IntegrableOn (fun s => pressureWeight p L s * (rayWeight L m a s * rayWeight L m b s)) (Ioi 0) := by
  have hI (i j : Fin n) := (stressKernel_integrable_all hp hL hL (add_pos (ha i) (hb j))).const_mul (m i * m j)
  refine (integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hI i j))).congr ?_
  exact Eventually.of_forall fun s => by
    dsimp only [pressureWeight,rayWeight]
    rw [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_add,Real.exp_add]
    ring

theorem rays_product_integrable {n : ℕ} {p L : ℝ} (hp : 0 < p) (_hp₂ : p ≤ 2) (hL : 0 < L)
    (m a b : Fin n → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) :
    IntegrableOn (fun s => pressureWeight p L s * (rayWeight L m a s * rayWeight L m b s)) (Ioi 0) :=
  rays_product_integrable_all hp hL m a b ha hb

noncomputable def pressureAt {n : ℕ} (p : ℝ) (S : AnchoredCircleSource (Fin n)) (i : Fin n) : ℝ :=
  ∫ s : ℝ in Ioi 0, pressureWeight p S.period s * ((leftRay S i s + S.mass i) * rightRay S i s)

noncomputable def pressureBefore {n : ℕ} (p : ℝ) (S : AnchoredCircleSource (Fin n)) (i : Fin n) : ℝ :=
  ∫ s : ℝ in Ioi 0, pressureWeight p S.period s * (leftRay S i s * (rightRay S i s + S.mass i))

theorem pressureAcrossGap {n : ℕ} (p : ℝ) (S : AnchoredCircleSource (Fin n)) {i j : Fin n}
    (hij : S.coordinate i < S.coordinate j)
    (h : ∀ k, ¬(S.coordinate i < S.coordinate k ∧ S.coordinate k < S.coordinate j)) :
    pressureAt p S i = pressureBefore p S j := by
  unfold pressureAt pressureBefore
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
    congrArg (fun x => pressureWeight p S.period s * x) (consecutive_ray_product S hij h hs)

private theorem rayDifference_integral {n : ℕ} {p : ℝ} (hp : 0 < p)
    (S : AnchoredCircleSource (Fin n)) (i : Fin n) :
    (∫ s : ℝ in Ioi 0, pressureWeight p S.period s * (rightRay S i s - leftRay S i s)) =
      p * (Real.pi / S.period) ^ (p + 1) *
        ∑ j ∈ Finset.univ.erase i, S.mass j * circleTorque p S.period (S.forwardDistance i j) := by
  let g (j : Fin n) (s : ℝ) := S.mass j * imageSlopeIntegrand p S.period (S.forwardDistance i j) s
  have hI (j : Fin n) (hj : j ∈ Finset.univ.erase i) : IntegrableOn (g j) (Ioi 0) := by
    have hN : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hA := imageSlopeTail_integrable hp S.period_pos (S.forwardDistance_pos i j)
    have hB := imageSlopeTail_integrable hp S.period_pos (S.forwardDistance_pos j i)
    rw [S.forwardDistance_flip hN] at hB
    apply ((hA.sub hB).const_mul (S.mass j)).congr
    exact Eventually.of_forall fun s => by
      dsimp only [g,imageSlopeIntegrand,Pi.sub_apply]
      ring
  have hE (s : ℝ) : pressureWeight p S.period s * (rightRay S i s - leftRay S i s) =
      ∑ j ∈ Finset.univ.erase i, g j s := by
    dsimp only [leftRay,rightRay,rayWeight]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),sub_self,add_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [S.forwardDistance_flip (Finset.mem_erase.mp hj).1.symm]
    dsimp only [g,imageSlopeIntegrand,periodicDen,pressureWeight]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => hE s),integral_finsetSum _ hI,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [g]
  rw [integral_const_mul,imageSlopeIntegral hp S.period_pos (S.forwardDistance_pos i j)
    (S.forwardDistance_lt_period (Finset.mem_erase.mp hj).1.symm)]
  ring

theorem pressureThroughSite_all {n : ℕ} {p : ℝ} (hp : 0 < p)
    (F : ACS12.Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) (i : Fin n) :
    pressureAt p C.source i = pressureBefore p C.source i := by
  let S := C.source
  let W := pressureWeight p S.period
  let A := leftRay S i
  let B := rightRay S i
  have hA : IntegrableOn (fun s => W s * A s) (Ioi 0) :=
    ray_integrable hp S.period_pos S.mass _ (fun j => S.forwardDistance_pos j i)
  have hB : IntegrableOn (fun s => W s * B s) (Ioi 0) :=
    ray_integrable hp S.period_pos S.mass _ (S.forwardDistance_pos i)
  have hAB : IntegrableOn (fun s => W s * (A s * B s)) (Ioi 0) :=
    rays_product_integrable_all hp S.period_pos S.mass _ _ (fun j => S.forwardDistance_pos j i) (S.forwardDistance_pos i)
  have hE₁ : pressureAt p S i = (∫ s : ℝ in Ioi 0, W s * (A s * B s)) +
      S.mass i * (∫ s : ℝ in Ioi 0, W s * B s) := by
    unfold pressureAt
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => W s * (A s * B s) + S.mass i * (W s * B s))
      (fun s _ => by dsimp only [W,A,B]; ring),integral_add hAB (hB.const_mul _),integral_const_mul]
  have hE₂ : pressureBefore p S i = (∫ s : ℝ in Ioi 0, W s * (A s * B s)) +
      S.mass i * (∫ s : ℝ in Ioi 0, W s * A s) := by
    unfold pressureBefore
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => W s * (A s * B s) + S.mass i * (W s * A s))
      (fun s _ => by dsimp only [W,A,B]; ring),integral_add hAB (hA.const_mul _),integral_const_mul]
  have h := rayDifference_integral hp S i
  have hT := F.chart_forward_torque_eq_zero C i
  change (∑ j ∈ Finset.univ.erase i, S.mass j * circleTorque p S.period (S.forwardDistance i j)) = 0 at hT
  rw [hT,mul_zero,setIntegral_congr_fun measurableSet_Ioi (g := fun s => W s * B s - W s * A s)
    (fun s _ => by dsimp only [W,A,B]; ring),integral_sub hB hA] at h
  rw [hE₁,hE₂,sub_eq_zero.mp h]


/-- Every cut of the same physical source has the same full stress. -/
theorem pressure_constant_all {n : ℕ} {p : ℝ} (hp : 0 < p)
    (F : ACS12.Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (i j : Fin n) : pressureAt p C.source i = pressureAt p C.source j := by
  let S := C.source
  let σ := Tuple.sort S.coordinate
  let a := S.coordinate ∘ σ
  have ha : StrictMono a := (Tuple.monotone_sort S.coordinate).strictMono_of_injective
    (S.coordinate_injective.comp σ.injective)
  have hStep (k : ℕ) (hk : k + 1 < n) :
      pressureAt p S (σ ⟨k,hk.trans' (Nat.lt_succ_self k)⟩) =
        pressureAt p S (σ ⟨k + 1,hk⟩) := by
    let l : Fin n := ⟨k,hk.trans' (Nat.lt_succ_self k)⟩
    let r : Fin n := ⟨k + 1,hk⟩
    have hlr : l < r := Nat.lt_succ_self k
    have hBetween (z : Fin n) : ¬(S.coordinate (σ l) < S.coordinate z ∧ S.coordinate z < S.coordinate (σ r)) := by
      rintro ⟨hL,hR⟩
      let t := σ.symm z
      have ht : σ t = z := σ.apply_symm_apply z
      rw [← ht] at hL hR
      have hLt : l < t := ha.lt_iff_lt.mp hL
      have hTr : t < r := ha.lt_iff_lt.mp hR
      change k < t.val at hLt
      change t.val < k + 1 at hTr
      omega
    exact (pressureAcrossGap p S (ha hlr) hBetween).trans (pressureThroughSite_all hp F C (σ r)).symm
  have hn : 0 < n := i.isLt.pos
  have hAll (k : ℕ) (hk : k < n) :
      pressureAt p S (σ ⟨k,hk⟩) = pressureAt p S (σ ⟨0,hn⟩) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      exact (hStep k hk).symm.trans (ih (Nat.lt_of_succ_lt hk))
  have hI := hAll (σ.symm i).val (σ.symm i).isLt
  have hJ := hAll (σ.symm j).val (σ.symm j).isLt
  simpa only [Fin.eta,Equiv.apply_symm_apply] using hI.trans hJ.symm

theorem pressureThroughSite {n : ℕ} {p : ℝ} (hp : 0 < p) (_hp₂ : p ≤ 2)
    (F : ACS12.Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) (i : Fin n) :
    pressureAt p C.source i = pressureBefore p C.source i :=
  pressureThroughSite_all hp F C i

theorem pressure_constant {n : ℕ} {p : ℝ} (hp : 0 < p) (_hp₂ : p ≤ 2)
    (F : ACS12.Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    (i j : Fin n) : pressureAt p C.source i = pressureAt p C.source j :=
  pressure_constant_all hp F C i j

end ACS12.Pressure
