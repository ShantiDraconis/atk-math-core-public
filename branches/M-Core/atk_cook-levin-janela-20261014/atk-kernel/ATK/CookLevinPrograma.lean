import ATK.CookLevinMolde
import ATK.GeradorArit

/-!
# ATK — Cook–Levin, marco CL4b-4d: o programa da redução

* `aritP`: calcula nos contadores `N = |w|`, `Mq = q(N)`, `E2 = 2N + 2`, `X = E2 + Mq`,
  `TT = time(X)`, `T1 = TT + 1`, `TP = (TT+1)·P + D + 1`, `SS = X + TP` e `S − c`;
* `progCL`: `aritP` seguido do programa do molde (`comp formulaT`).

**Nada aqui prova Cook–Levin sozinho; CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinPrograma

set_option linter.unusedSectionVars false

open Function ATK.Gerador ATK.CookLevinMolde

noncomputable section

variable {C : ℕ}

/-! ### Blocos auxiliares -/

/-- `r += k`. -/
def incs (k : ℕ) (r : Rg C) : Prog (Rg C) := seqs (List.replicate k (.inc r))

/-- `r -= k`. -/
def decs (k : ℕ) (r : Rg C) : Prog (Rg C) := seqs (List.replicate k (.dec r))

theorem run_incs (w : List Bool) (r : Rg C) :
    ∀ (k : ℕ) (s : St (Rg C)), run w (incs k r) s = ⟨update s.regs r (s.regs r + k), s.out⟩
  | 0, s => by simp [incs, seqs, run]
  | k + 1, s => by
    have := run_incs w r k ⟨update s.regs r (s.regs r + 1), s.out⟩
    simp only [incs, seqs, List.replicate_succ, List.foldr_cons, run] at this ⊢
    rw [this]
    simp only [update_self, update_idem, St.mk.injEq, and_true]
    congr 1
    omega

theorem cost_incs (w : List Bool) (r : Rg C) :
    ∀ (k : ℕ) (s : St (Rg C)), cost w (incs k r) s = k
  | 0, s => by simp [incs, seqs, cost]
  | k + 1, s => by
    have := cost_incs w r k (run w (.inc r) s)
    simp only [incs, seqs, List.replicate_succ, List.foldr_cons, cost_seq, cost_inc] at this ⊢
    rw [this]
    omega

theorem run_decs (w : List Bool) (r : Rg C) :
    ∀ (k : ℕ) (s : St (Rg C)), run w (decs k r) s = ⟨update s.regs r (s.regs r - k), s.out⟩
  | 0, s => by simp [decs, seqs, run]
  | k + 1, s => by
    have := run_decs w r k ⟨update s.regs r (s.regs r - 1), s.out⟩
    simp only [decs, seqs, List.replicate_succ, List.foldr_cons, run] at this ⊢
    rw [this]
    simp only [update_self, update_idem, St.mk.injEq, and_true]
    congr 1
    omega

theorem cost_decs (w : List Bool) (r : Rg C) :
    ∀ (k : ℕ) (s : St (Rg C)), cost w (decs k r) s = k
  | 0, s => by simp [decs, seqs, cost]
  | k + 1, s => by
    have := cost_decs w r k (run w (.dec r) s)
    simp only [decs, seqs, List.replicate_succ, List.foldr_cons, cost_seq] at this ⊢
    rw [this]
    simp [cost]
    omega

theorem run_conta (w : List Bool) (r : Rg C) (s : St (Rg C)) :
    run w (.forIn (.inc r) (.inc r)) s = ⟨update s.regs r (s.regs r + w.length), s.out⟩ := by
  have it : ∀ (l : List Bool) (s : St (Rg C)), l.foldl (fun s b => if b then run w (.inc r) s
      else run w (.inc r) s) s = ⟨update s.regs r (s.regs r + l.length), s.out⟩ := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons b l ih =>
      intro s
      rw [List.foldl_cons]
      have e : (if b then run w (.inc r) s else run w (.inc r) s) = run w (.inc r) s := by
        cases b <;> rfl
      rw [e, ih]
      simp only [run, update_self, update_idem, St.mk.injEq, and_true, List.length_cons]
      congr 1
      omega
  exact it w s

theorem cost_conta (w : List Bool) (r : Rg C) (s : St (Rg C)) :
    cost w (.forIn (.inc r) (.inc r)) s = 5 * w.length + 3 := by
  have it : ∀ (l : List Bool) (s : St (Rg C)), costIn (cost w (.inc r)) (cost w (.inc r))
      (run w (.inc r)) (run w (.inc r)) l s = 3 * l.length := by
    intro l
    induction l with
    | nil => intro s; simp [costIn]
    | cons b l ih =>
      intro s
      rw [costIn_cons]
      cases b <;> simp [cost_inc, ih] <;> ring
  rw [cost_forIn, it]
  ring

/-! ### O programa aritmético -/

/-- `S − c` para cada `c < C`. -/
def smP (C : ℕ) : Prog (Rg C) :=
  seqs ((List.range C).map fun c => .seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c)))

/-- O programa aritmético, antes de `S − c`. -/
def aritA (qc tc : List ℕ) (P D : ℕ) : Prog (Rg C) :=
  .seq (.forIn (.inc Rg.N) (.inc Rg.N))
  (.seq (evalP qc Rg.N Rg.Mq Rg.pw Rg.tm)
  (.seq (addTo Rg.N Rg.E2) (.seq (addTo Rg.N Rg.E2) (.seq (.inc Rg.E2) (.seq (.inc Rg.E2)
  (.seq (addTo Rg.E2 Rg.X) (.seq (addTo Rg.Mq Rg.X)
  (.seq (evalP tc Rg.X Rg.TT Rg.pw Rg.tm)
  (.seq (addTo Rg.TT Rg.T1) (.seq (.inc Rg.T1)
  (.seq (addMul P Rg.T1 Rg.TP) (.seq (incs (D + 1) Rg.TP)
  (.seq (addTo Rg.X Rg.SS) (addTo Rg.TP Rg.SS))))))))))))))

/-- O programa aritmético. -/
def aritP (qc tc : List ℕ) (P D : ℕ) : Prog (Rg C) := .seq (aritA qc tc P D) (smP C)

/-- Os valores calculados. -/
structure Vals (C : ℕ) (n qv tv P D : ℕ) (g : Rg C → ℕ) : Prop where
  N : g Rg.N = n
  Mq : g Rg.Mq = qv
  E2 : g Rg.E2 = 2 * n + 2
  X : g Rg.X = 2 * n + 2 + qv
  TT : g Rg.TT = tv
  T1 : g Rg.T1 = tv + 1
  TP : g Rg.TP = P * (tv + 1) + (D + 1)
  SS : g Rg.SS = 2 * n + 2 + qv + (P * (tv + 1) + (D + 1))
  pw : g Rg.pw = 0
  tm : g Rg.tm = 0
  t : g Rg.t = 0
  j : g Rg.j = 0
  i : g Rg.i = 0

theorem s0_regs (r : Rg C) : (s0 : St (Rg C)).regs r = 0 := rfl

theorem run_seqP (w : List Bool) (p q : Prog (Rg C)) (s : St (Rg C)) :
    run w (.seq p q) s = run w q (run w p s) := rfl

theorem run_incP (w : List Bool) (r : Rg C) (s : St (Rg C)) :
    run w (.inc r) s = ⟨update s.regs r (s.regs r + 1), s.out⟩ := rfl

theorem run_aritA (w : List Bool) (qc tc : List ℕ) (P D : ℕ) :
    (run w (aritA (C := C) qc tc P D) s0).out = [] ∧
    Vals C w.length (horn w.length qc) (horn (2 * w.length + 2 + horn w.length qc) tc) P D
      (run w (aritA qc tc P D) s0).regs ∧
    ∀ c : Fin C, (run w (aritA (C := C) qc tc P D) s0).regs (.inr c) = 0 := by
  have ev := fun (x acc : Rg C) (h1 : x ≠ acc) (h2 : x ≠ Rg.pw) (h3 : x ≠ Rg.tm)
    (h4 : acc ≠ Rg.pw) (h5 : acc ≠ Rg.tm) => run_evalP h1 h2 h3 h4 h5 (by simp) w
  simp only [aritA, run_seqP, run_incP, run_conta, ev Rg.N Rg.Mq (by simp) (by simp) (by simp) (by simp)
      (by simp),
    ev Rg.X Rg.TT (by simp) (by simp) (by simp) (by simp) (by simp),
    run_addTo w (show (Rg.N : Rg C) ≠ Rg.E2 by simp),
    run_addTo w (show (Rg.E2 : Rg C) ≠ Rg.X by simp),
    run_addTo w (show (Rg.Mq : Rg C) ≠ Rg.X by simp),
    run_addTo w (show (Rg.TT : Rg C) ≠ Rg.T1 by simp),
    run_addTo w (show (Rg.X : Rg C) ≠ Rg.SS by simp),
    run_addTo w (show (Rg.TP : Rg C) ≠ Rg.SS by simp),
    run_addMul w (show (Rg.T1 : Rg C) ≠ Rg.TP by simp), run_incs]
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun c => ?_⟩
  all_goals (simp [s0_regs]; try ring_nf; try simp)

theorem run_seqs_cons (w : List Bool) (p : Prog (Rg C)) (ps : List (Prog (Rg C)))
    (s : St (Rg C)) : run w (seqs (p :: ps)) s = run w (seqs ps) (run w p s) := rfl

theorem cost_seqs_cons (w : List Bool) (p : Prog (Rg C)) (ps : List (Prog (Rg C)))
    (s : St (Rg C)) : cost w (seqs (p :: ps)) s = cost w p s + cost w (seqs ps) (run w p s) := rfl

theorem sm_lt {c : ℕ} (hc : c < C) : (Rg.sm c : Rg C) = .inr ⟨c, hc⟩ := by
  simp [Rg.sm, hc]

theorem sm_ne_SS {c : ℕ} (hc : c < C) : (Rg.sm c : Rg C) ≠ Rg.SS := by
  rw [sm_lt hc]; simp

theorem sm_inj {c c' : ℕ} (hc : c < C) (hc' : c' < C) (h : (Rg.sm c : Rg C) = Rg.sm c') :
    c = c' := by
  rw [sm_lt hc, sm_lt hc'] at h
  simpa using h

/-- Um passo de `smP`. -/
theorem run_smStep (w : List Bool) {c : ℕ} (hc : c < C) (s : St (Rg C)) :
    run w (.seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c))) s =
      ⟨update s.regs (Rg.sm c) (s.regs (Rg.sm c) + s.regs Rg.SS - c), s.out⟩ := by
  rw [run_seqP, run_addTo w (Ne.symm (sm_ne_SS hc)), run_decs]
  simp

theorem run_smL (w : List Bool) :
    ∀ (l : List ℕ), (∀ c ∈ l, c < C) → l.Nodup → ∀ s : St (Rg C),
      (∀ c ∈ l, s.regs (Rg.sm c) = 0) →
      (run w (seqs (l.map fun c => .seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c)))) s).out =
        s.out ∧
      (∀ r, (∀ c ∈ l, r ≠ Rg.sm c) →
        (run w (seqs (l.map fun c => .seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c)))) s).regs r =
          s.regs r) ∧
      ∀ c ∈ l, (run w (seqs (l.map fun c => .seq (addTo Rg.SS (Rg.sm c))
        (decs c (Rg.sm c)))) s).regs (Rg.sm c) = s.regs Rg.SS - c
  | [], _, _, s, _ => by simp [seqs, run]
  | c :: l, hl, hnd, s, h0 => by
    have hc : c < C := hl c (List.mem_cons_self ..)
    have hcl : c ∉ l := (List.nodup_cons.mp hnd).1
    set s1 := run w (.seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c))) s with hs1
    have e1 := run_smStep w hc s
    have hSS : s1.regs Rg.SS = s.regs Rg.SS := by
      rw [hs1, e1]; simp [update_of_ne (Ne.symm (sm_ne_SS hc))]
    obtain ⟨i1, i2, i3⟩ := run_smL w l (fun c' h => hl c' (List.mem_cons_of_mem _ h))
      (List.nodup_cons.mp hnd).2 s1 (fun c' hc' => by
        have hne : (Rg.sm c' : Rg C) ≠ Rg.sm c := fun e =>
          hcl (sm_inj hc (hl c' (List.mem_cons_of_mem _ hc')) e.symm ▸ hc')
        rw [hs1, e1]; simp [update_of_ne hne, h0 c' (List.mem_cons_of_mem _ hc')])
    rw [List.map_cons, run_seqs_cons, ← hs1]
    refine ⟨by rw [i1, hs1, e1], fun r hr => ?_, fun c' hc' => ?_⟩
    · rw [i2 r (fun c' h => hr c' (List.mem_cons_of_mem _ h)), hs1, e1]
      simp [update_of_ne (hr c (List.mem_cons_self ..))]
    · rcases List.mem_cons.mp hc' with rfl | hc'
      · have hnot : ∀ c'' ∈ l, (Rg.sm c' : Rg C) ≠ Rg.sm c'' := fun c'' h e =>
          hcl (sm_inj hc (hl c'' (List.mem_cons_of_mem _ h)) e ▸ h)
        rw [i2 _ hnot, hs1, e1]
        simp [h0 c' (List.mem_cons_self ..)]
      · rw [i3 c' hc', hSS]

theorem run_smP (w : List Bool) (s : St (Rg C)) (h0 : ∀ c : Fin C, s.regs (.inr c) = 0) :
    (run w (smP C) s).out = s.out ∧
    (∀ a : Fin 13, (run w (smP C) s).regs (.inl a) = s.regs (.inl a)) ∧
    ∀ c < C, (run w (smP C) s).regs (Rg.sm c) = s.regs Rg.SS - c := by
  obtain ⟨i1, i2, i3⟩ := run_smL w (List.range C) (fun c h => List.mem_range.mp h)
    List.nodup_range s (fun c h => by rw [sm_lt (List.mem_range.mp h)]; exact h0 _)
  refine ⟨i1, fun a => i2 _ (fun c h => ?_), fun c hc => i3 c (List.mem_range.mpr hc)⟩
  rw [sm_lt (List.mem_range.mp h)]
  simp

theorem cost_smL (w : List Bool) (B : ℕ) :
    ∀ (l : List ℕ), (∀ c ∈ l, c < C) → ∀ s : St (Rg C), s.regs Rg.SS ≤ B →
      cost w (seqs (l.map fun c => .seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c)))) s ≤
        l.length * (5 * B + 3 + C)
  | [], _, s, _ => by simp [seqs, cost]
  | c :: l, hl, s, hB => by
    have hc : c < C := hl c (List.mem_cons_self ..)
    have hSS : (run w (.seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c))) s).regs Rg.SS =
        s.regs Rg.SS := by
      rw [run_smStep w hc]; simp [update_of_ne (Ne.symm (sm_ne_SS hc))]
    have ih := cost_smL w B l (fun c' h => hl c' (List.mem_cons_of_mem _ h))
      (run w (.seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c))) s) (by rw [hSS]; exact hB)
    have hstep : cost w (.seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c))) s =
        5 * s.regs Rg.SS + 3 + c := by
      rw [cost_seq, cost_addTo, cost_decs]
    rw [List.map_cons, cost_seqs_cons, hstep, List.length_cons]
    have : 5 * s.regs Rg.SS ≤ 5 * B := Nat.mul_le_mul_left _ hB
    calc 5 * s.regs Rg.SS + 3 + c + cost w (seqs (l.map fun c =>
            .seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c))))
            (run w (.seq (addTo Rg.SS (Rg.sm c)) (decs c (Rg.sm c))) s)
          ≤ (5 * B + 3 + C) + l.length * (5 * B + 3 + C) := by omega
      _ = (l.length + 1) * (5 * B + 3 + C) := by ring

/-! ### Custo da aritmética -/

/-- Limite do custo de `evalP`. -/
def Ecost (cs : List ℕ) (V : ℕ) : ℕ :=
  5 + cs.length * (cs.sum * (5 * V ^ cs.length + 3) + 19 * V ^ cs.length + 9) + V ^ cs.length

theorem cost_evalP_le (w : List Bool) {x acc : Rg C} (h1 : x ≠ acc) (h2 : x ≠ Rg.pw)
    (h3 : x ≠ Rg.tm) (h4 : acc ≠ Rg.pw) (h5 : acc ≠ Rg.tm) (cs : List ℕ) (s : St (Rg C))
    (V : ℕ) (ha : s.regs acc = 0) (hp : s.regs Rg.pw = 0) (ht : s.regs Rg.tm = 0)
    (hx : s.regs x + 1 ≤ V) : cost w (evalP cs x acc Rg.pw Rg.tm) s ≤ Ecost cs V := by
  have h := cost_evalP h1 h2 h3 h4 h5 (by simp) w cs s
  have hk : (s.regs x + 1) ^ cs.length ≤ V ^ cs.length := Nat.pow_le_pow_left hx _
  have hk1 : cs.sum * (5 * (s.regs x + 1) ^ cs.length + 3) ≤ cs.sum * (5 * V ^ cs.length + 3) :=
    Nat.mul_le_mul_left _ (by omega)
  have hk2 : cs.length * (cs.sum * (5 * (s.regs x + 1) ^ cs.length + 3) +
      19 * (s.regs x + 1) ^ cs.length + 9) ≤
      cs.length * (cs.sum * (5 * V ^ cs.length + 3) + 19 * V ^ cs.length + 9) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [ha, hp, ht] at h
  unfold Ecost
  omega

theorem cost_seqP (w : List Bool) (p q : Prog (Rg C)) (s : St (Rg C)) :
    cost w (.seq p q) s = cost w p s + cost w q (run w p s) := rfl

set_option maxHeartbeats 4000000 in
theorem cost_aritA (w : List Bool) (qc tc : List ℕ) (P D V : ℕ)
    (hV : 2 * w.length + 2 + horn w.length qc +
      (P * (horn (2 * w.length + 2 + horn w.length qc) tc + 1) + (D + 1)) +
      horn (2 * w.length + 2 + horn w.length qc) tc + 1 ≤ V) :
    cost w (aritA (C := C) qc tc P D) s0 ≤
      (5 * V + 3) * 7 + 3 + Ecost qc V + Ecost tc V + P * (5 * V + 3) + (D + 1) := by
  have ev := fun (x acc : Rg C) (h1 : x ≠ acc) (h2 : x ≠ Rg.pw) (h3 : x ≠ Rg.tm)
    (h4 : acc ≠ Rg.pw) (h5 : acc ≠ Rg.tm) => run_evalP h1 h2 h3 h4 h5 (by simp) w
  set n := w.length with hn
  set qv := horn n qc with hqv
  set tv := horn (2 * n + 2 + qv) tc with htv
  rw [aritA, cost_seqP, cost_conta]
  set S1 := run w (.forIn (.inc Rg.N) (.inc Rg.N)) (s0 : St (Rg C)) with hS1
  have f1 : S1.regs = update (fun _ => 0) Rg.N n := by rw [hS1, run_conta]; simp [s0, ← hn]
  rw [cost_seqP]
  have c2 := cost_evalP_le w (x := Rg.N) (acc := Rg.Mq) (by simp) (by simp) (by simp) (by simp)
    (by simp) qc S1 V (by simp [f1]) (by simp [f1]) (by simp [f1]) (by simp [f1]; omega)
  set S2 := run w (evalP qc Rg.N Rg.Mq Rg.pw Rg.tm) S1 with hS2
  have f2 : S2.regs = update (update (update S1.regs Rg.Mq qv) Rg.pw 0) Rg.tm 0 := by
    rw [hS2, ev Rg.N Rg.Mq (by simp) (by simp) (by simp) (by simp) (by simp)]; simp [f1, hqv]
  rw [cost_seqP, cost_addTo]
  set S3 := run w (addTo Rg.N Rg.E2) S2 with hS3
  have f3 : S3.regs = update S2.regs Rg.E2 (S2.regs Rg.E2 + S2.regs Rg.N) := by
    rw [hS3, run_addTo w (show (Rg.N : Rg C) ≠ Rg.E2 by simp)]
  rw [cost_seqP, cost_addTo]
  set S4 := run w (addTo Rg.N Rg.E2) S3 with hS4
  have f4 : S4.regs = update S3.regs Rg.E2 (S3.regs Rg.E2 + S3.regs Rg.N) := by
    rw [hS4, run_addTo w (show (Rg.N : Rg C) ≠ Rg.E2 by simp)]
  rw [cost_seqP, cost_inc]
  set S5 := run w (.inc Rg.E2) S4 with hS5
  have f5 : S5.regs = update S4.regs Rg.E2 (S4.regs Rg.E2 + 1) := by rw [hS5, run_incP]
  rw [cost_seqP, cost_inc]
  set S6 := run w (.inc Rg.E2) S5 with hS6
  have f6 : S6.regs = update S5.regs Rg.E2 (S5.regs Rg.E2 + 1) := by rw [hS6, run_incP]
  rw [cost_seqP, cost_addTo]
  set S7 := run w (addTo Rg.E2 Rg.X) S6 with hS7
  have f7 : S7.regs = update S6.regs Rg.X (S6.regs Rg.X + S6.regs Rg.E2) := by
    rw [hS7, run_addTo w (show (Rg.E2 : Rg C) ≠ Rg.X by simp)]
  rw [cost_seqP, cost_addTo]
  set S8 := run w (addTo Rg.Mq Rg.X) S7 with hS8
  have f8 : S8.regs = update S7.regs Rg.X (S7.regs Rg.X + S7.regs Rg.Mq) := by
    rw [hS8, run_addTo w (show (Rg.Mq : Rg C) ≠ Rg.X by simp)]
  have vN : S8.regs Rg.N = n := by simp [f8, f7, f6, f5, f4, f3, f2, f1]
  have vMq : S8.regs Rg.Mq = qv := by simp [f8, f7, f6, f5, f4, f3, f2, f1]
  have vE2 : S8.regs Rg.E2 = 2 * n + 2 := by simp [f8, f7, f6, f5, f4, f3, f2, f1]; ring
  have vX : S8.regs Rg.X = 2 * n + 2 + qv := by simp [f8, f7, f6, f5, f4, f3, f2, f1]; ring
  have hN3 : S2.regs Rg.N = n := by simp [f2, f1]
  have hN4 : S3.regs Rg.N = n := by simp [f3, f2, f1]
  have hE7 : S6.regs Rg.E2 = 2 * n + 2 := by simp [f6, f5, f4, f3, f2, f1]; ring
  have hMq8 : S7.regs Rg.Mq = qv := by simp [f7, f6, f5, f4, f3, f2, f1]
  rw [cost_seqP]
  have c9 := cost_evalP_le w (x := Rg.X) (acc := Rg.TT) (by simp) (by simp) (by simp) (by simp)
    (by simp) tc S8 V (by simp [f8, f7, f6, f5, f4, f3, f2, f1])
    (by simp [f8, f7, f6, f5, f4, f3, f2, f1]) (by simp [f8, f7, f6, f5, f4, f3, f2, f1])
    (by rw [vX]; omega)
  set S9 := run w (evalP tc Rg.X Rg.TT Rg.pw Rg.tm) S8 with hS9
  have f9 : S9.regs = update (update (update S8.regs Rg.TT tv) Rg.pw 0) Rg.tm 0 := by
    rw [hS9, ev Rg.X Rg.TT (by simp) (by simp) (by simp) (by simp) (by simp), vX]
  rw [cost_seqP, cost_addTo]
  set S10 := run w (addTo Rg.TT Rg.T1) S9 with hS10
  have f10 : S10.regs = update S9.regs Rg.T1 (S9.regs Rg.T1 + S9.regs Rg.TT) := by
    rw [hS10, run_addTo w (show (Rg.TT : Rg C) ≠ Rg.T1 by simp)]
  rw [cost_seqP, cost_inc]
  set S11 := run w (.inc Rg.T1) S10 with hS11
  have f11 : S11.regs = update S10.regs Rg.T1 (S10.regs Rg.T1 + 1) := by rw [hS11, run_incP]
  rw [cost_seqP, cost_addMul w (show (Rg.T1 : Rg C) ≠ Rg.TP by simp)]
  set S12 := run w (addMul P Rg.T1 Rg.TP) S11 with hS12
  have f12 : S12.regs = update S11.regs Rg.TP (S11.regs Rg.TP + P * S11.regs Rg.T1) := by
    rw [hS12, run_addMul w (show (Rg.T1 : Rg C) ≠ Rg.TP by simp)]
  rw [cost_seqP, cost_incs]
  set S13 := run w (incs (D + 1) Rg.TP) S12 with hS13
  have f13 : S13.regs = update S12.regs Rg.TP (S12.regs Rg.TP + (D + 1)) := by
    rw [hS13, run_incs]
  rw [cost_seqP, cost_addTo, cost_addTo]
  have hTT : S9.regs Rg.TT = tv := by simp [f9]
  have hT1 : S11.regs Rg.T1 = tv + 1 := by
    simp [f11, f10, f9, f8, f7, f6, f5, f4, f3, f2, f1]
  have hX13 : S13.regs Rg.X = 2 * n + 2 + qv := by
    simp [f13, f12, f11, f10, f9]; exact vX
  have hTP14 : (run w (addTo Rg.X Rg.SS) S13).regs Rg.TP = P * (tv + 1) + (D + 1) := by
    rw [run_addTo w (show (Rg.X : Rg C) ≠ Rg.SS by simp)]
    simp [f13, f12, hT1, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2, f1]
  rw [hN3, hN4, hE7, hMq8, hTT, hT1, hX13, hTP14]
  have b1 : 5 * n + 3 ≤ 5 * V + 3 := by omega
  have b2 : 5 * (2 * n + 2) + 3 ≤ 5 * V + 3 := by omega
  have b3 : 5 * qv + 3 ≤ 5 * V + 3 := by omega
  have b4 : 5 * tv + 3 ≤ 5 * V + 3 := by omega
  have b5 : P * (5 * (tv + 1) + 3) ≤ P * (5 * V + 3) := Nat.mul_le_mul_left _ (by omega)
  have b6 : 5 * (2 * n + 2 + qv) + 3 ≤ 5 * V + 3 := by omega
  have b7 : 5 * (P * (tv + 1) + (D + 1)) + 3 ≤ 5 * V + 3 := by omega
  omega

theorem cost_aritP (w : List Bool) (qc tc : List ℕ) (P D V : ℕ)
    (hV : 2 * w.length + 2 + horn w.length qc +
      (P * (horn (2 * w.length + 2 + horn w.length qc) tc + 1) + (D + 1)) +
      horn (2 * w.length + 2 + horn w.length qc) tc + 1 ≤ V) :
    cost w (aritP (C := C) qc tc P D) s0 ≤
      (5 * V + 3) * 7 + 3 + Ecost qc V + Ecost tc V + P * (5 * V + 3) + (D + 1) +
        C * (5 * V + 3 + C) := by
  rw [aritP, cost_seqP]
  have h1 := cost_aritA (C := C) w qc tc P D V hV
  obtain ⟨-, a2, -⟩ := run_aritA (C := C) w qc tc P D
  have h2 := cost_smL (C := C) w V (List.range C) (fun c h => List.mem_range.mp h)
    (run w (aritA qc tc P D) s0) (by rw [a2.SS]; omega)
  simp only [List.length_range] at h2
  exact Nat.add_le_add h1 h2

/-- Os valores finais dos contadores. -/
theorem run_aritP (w : List Bool) (qc tc : List ℕ) (P D : ℕ) :
    (run w (aritP (C := C) qc tc P D) s0).out = [] ∧
    Vals C w.length (horn w.length qc) (horn (2 * w.length + 2 + horn w.length qc) tc) P D
      (run w (aritP qc tc P D) s0).regs ∧
    SmOK (run w (aritP (C := C) qc tc P D) s0).regs := by
  obtain ⟨a1, a2, a3⟩ := run_aritA (C := C) w qc tc P D
  obtain ⟨b1, b2, b3⟩ := run_smP w _ a3
  rw [aritP, run_seqP]
  refine ⟨by rw [b1, a1], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun c hc => ?_⟩
  · rw [b2]; exact a2.N
  · rw [b2]; exact a2.Mq
  · rw [b2]; exact a2.E2
  · rw [b2]; exact a2.X
  · rw [b2]; exact a2.TT
  · rw [b2]; exact a2.T1
  · rw [b2]; exact a2.TP
  · rw [b2]; exact a2.SS
  · rw [b2]; exact a2.pw
  · rw [b2]; exact a2.tm
  · rw [b2]; exact a2.t
  · rw [b2]; exact a2.j
  · rw [b2]; exact a2.i
  · rw [b3 c hc, b2]

/-- Todos os contadores finais são `≤ V`. -/
theorem regs_le_V (w : List Bool) (qc tc : List ℕ) (P D V : ℕ)
    (hV : 2 * w.length + 2 + horn w.length qc +
      (P * (horn (2 * w.length + 2 + horn w.length qc) tc + 1) + (D + 1)) +
      horn (2 * w.length + 2 + horn w.length qc) tc + 1 ≤ V) :
    ∀ r, (run w (aritP (C := C) qc tc P D) s0).regs r ≤ V := by
  obtain ⟨-, v, hsm⟩ := run_aritP (C := C) w qc tc P D
  rintro (a | c)
  · fin_cases a
    · exact le_trans (le_of_eq v.N) (by omega)
    · exact le_trans (le_of_eq v.Mq) (by omega)
    · exact le_trans (le_of_eq v.X) (by omega)
    · exact le_trans (le_of_eq v.TT) (by omega)
    · exact le_trans (le_of_eq v.T1) (by omega)
    · exact le_trans (le_of_eq v.SS) (by omega)
    · exact le_trans (le_of_eq v.TP) (by omega)
    · exact le_trans (le_of_eq v.pw) (by omega)
    · exact le_trans (le_of_eq v.tm) (by omega)
    · exact le_trans (le_of_eq v.t) (by omega)
    · exact le_trans (le_of_eq v.j) (by omega)
    · exact le_trans (le_of_eq v.i) (by omega)
    · exact le_trans (le_of_eq v.E2) (by omega)
  · have := hsm c.val c.isLt
    rw [sm_lt c.isLt] at this
    rw [this, v.SS]
    omega

end

end ATK.CookLevinPrograma

#print axioms ATK.CookLevinPrograma.incs
#print axioms ATK.CookLevinPrograma.decs
#print axioms ATK.CookLevinPrograma.run_incs
#print axioms ATK.CookLevinPrograma.cost_incs
#print axioms ATK.CookLevinPrograma.run_decs
#print axioms ATK.CookLevinPrograma.cost_decs
#print axioms ATK.CookLevinPrograma.run_conta
#print axioms ATK.CookLevinPrograma.cost_conta
#print axioms ATK.CookLevinPrograma.smP
#print axioms ATK.CookLevinPrograma.aritA
#print axioms ATK.CookLevinPrograma.aritP
#print axioms ATK.CookLevinPrograma.Vals
#print axioms ATK.CookLevinPrograma.s0_regs
#print axioms ATK.CookLevinPrograma.run_seqP
#print axioms ATK.CookLevinPrograma.run_incP
#print axioms ATK.CookLevinPrograma.run_aritA
#print axioms ATK.CookLevinPrograma.run_seqs_cons
#print axioms ATK.CookLevinPrograma.cost_seqs_cons
#print axioms ATK.CookLevinPrograma.sm_lt
#print axioms ATK.CookLevinPrograma.sm_ne_SS
#print axioms ATK.CookLevinPrograma.sm_inj
#print axioms ATK.CookLevinPrograma.run_smStep
#print axioms ATK.CookLevinPrograma.run_smL
#print axioms ATK.CookLevinPrograma.run_smP
#print axioms ATK.CookLevinPrograma.cost_smL
#print axioms ATK.CookLevinPrograma.Ecost
#print axioms ATK.CookLevinPrograma.cost_evalP_le
#print axioms ATK.CookLevinPrograma.cost_seqP
#print axioms ATK.CookLevinPrograma.cost_aritA
#print axioms ATK.CookLevinPrograma.cost_aritP
#print axioms ATK.CookLevinPrograma.run_aritP
#print axioms ATK.CookLevinPrograma.regs_le_V
