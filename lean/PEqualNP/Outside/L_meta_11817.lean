import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11817
open PEqualNP.CircuitLowerBounds

-- The wires of a gate list on a seven-bit input, and the function carried by wire j.
def wr (gs : List Gate) (x : Fin 7 → Bool) : List Bool :=
  Circuit.wires ⟨gs, 0⟩ (List.ofFn x)

def hw (gs : List Gate) (j : ℕ) (x : Fin 7 → Bool) : Bool := (wr gs x).getD j false

theorem wr_snoc (gs : List Gate) (g : Gate) (x : Fin 7 → Bool) :
    wr (gs ++ [g]) x
      = wr gs x ++ [g.op.eval (g.inputs.map fun i => (wr gs x).getD i false)] := by
  simp [wr, Circuit.wires, List.foldl_append]

theorem wr_length (gs : List Gate) (x : Fin 7 → Bool) : (wr gs x).length = 7 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr, Circuit.wires]
  | append_singleton gs g ih => rw [wr_snoc]; simp [ih]; omega

theorem hw_snoc_lt (gs : List Gate) (g : Gate) (j : ℕ) (x : Fin 7 → Bool)
    (h : j < 7 + gs.length) : hw (gs ++ [g]) j x = hw gs j x := by
  unfold hw
  rw [wr_snoc, List.getD_append _ _ _ _ (by rw [wr_length]; exact h)]

theorem hw_input (gs : List Gate) (j : Fin 7) (x : Fin 7 → Bool) : hw gs j x = x j := by
  induction gs using List.reverseRecOn with
  | nil =>
    simp only [hw, wr, Circuit.wires, List.foldl_nil]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
    fin_cases j <;> rfl
  | append_singleton gs g ih =>
    rw [hw_snoc_lt _ _ _ _ (by have := j.isLt; omega)]; exact ih

theorem hw_big (gs : List Gate) (j : ℕ) (x : Fin 7 → Bool) (h : 7 + gs.length ≤ j) :
    hw gs j x = false := by
  unfold hw
  exact List.getD_eq_default _ _ (by rw [wr_length]; exact h)

theorem hw_gate (gs : List Gate) : ∀ (k : ℕ) (g : Gate) (x : Fin 7 → Bool), gs[k]? = some g →
    hw gs (7 + k) x
      = g.op.eval (g.inputs.map fun a => if a < 7 + k then hw gs a x else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro k g x h; simp at h
  | append_singleton gs g0 ih =>
    intro k g x h
    rcases Nat.lt_trichotomy k gs.length with hk | hk | hk
    · rw [List.getElem?_append_left hk] at h
      rw [hw_snoc_lt _ _ _ _ (by omega), ih k g x h]
      congr 1
      apply List.map_congr_left
      intro a _
      by_cases ha : a < 7 + k
      · rw [if_pos ha, if_pos ha, hw_snoc_lt _ _ _ _ (by omega)]
      · rw [if_neg ha, if_neg ha]
    · subst hk
      have hg : g0 = g := by simpa using h
      subst hg
      have h1 : hw (gs ++ [g0]) (7 + gs.length) x
          = g0.op.eval (g0.inputs.map fun i => (wr gs x).getD i false) := by
        unfold hw
        rw [wr_snoc, ← wr_length gs x]
        simp
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro a _
      by_cases ha : a < 7 + gs.length
      · rw [if_pos ha, hw_snoc_lt _ _ _ _ ha]; rfl
      · rw [if_neg ha]
        exact List.getD_eq_default _ _ (by rw [wr_length]; omega)
    · rw [List.getElem?_eq_none (by simp; omega)] at h
      simp at h

-- h is fixed on D by the features in S.
def Det {ι : Type} (D : (Fin 7 → Bool) → Prop) (Φ : ι → (Fin 7 → Bool) → Bool)
    (S : Finset ι) (h : (Fin 7 → Bool) → Bool) : Prop :=
  ∀ x y, D x → D y → (∀ s ∈ S, Φ s x = Φ s y) → h x = h y

theorem Det.mono {ι : Type} {D : (Fin 7 → Bool) → Prop} {Φ : ι → (Fin 7 → Bool) → Bool}
    {S T : Finset ι} {h : (Fin 7 → Bool) → Bool} (hd : Det D Φ S h) (hST : S ⊆ T) :
    Det D Φ T h :=
  fun x y hx hy hxy => hd x y hx hy (fun s hs => hxy s (hST hs))

theorem card_inter_range_le {E : Finset ℕ} (k : ℕ) :
    (E ∩ Finset.range k).card ≤ (E ∩ Finset.range (k + 1)).card :=
  Finset.card_le_card (Finset.inter_subset_inter_left
    (Finset.range_subset_range.2 (Nat.le_succ k)))

theorem card_inter_range_succ {E : Finset ℕ} (k : ℕ) (hk : k ∈ E) :
    (E ∩ Finset.range (k + 1)).card = (E ∩ Finset.range k).card + 1 := by
  have : E ∩ Finset.range (k + 1) = insert k (E ∩ Finset.range k) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : a = k
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h; exact ⟨hk, by omega⟩
      · exact ⟨h1, by omega⟩
  rw [this, Finset.card_insert_of_notMem (by simp)]

-- The counting step: wires 0 .. 7+k-1 carry supports whose unions are small.
theorem count_inv {ι : Type} [DecidableEq ι] (D : (Fin 7 → Bool) → Prop)
    (Φ : ι → (Fin 7 → Bool) → Bool) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hin : ∀ j : Fin 7, ∃ S : Finset ι, S.card ≤ 1 ∧ Det D Φ S (fun x => x j))
    (E : Finset ℕ)
    (hE : ∀ k g, gs[k]? = some g → k ∉ E →
      g.op = GateOp.not ∨ ∃ S : Finset ι, S.card ≤ 1 ∧ Det D Φ S (hw gs (7 + k))) :
    ∀ k, k ≤ gs.length → ∃ L : ℕ → Finset ι,
      (∀ j, j < 7 + k → Det D Φ (L j) (hw gs j)) ∧
      ∀ Wf : Finset ℕ, (∀ j ∈ Wf, j < 7 + k) →
        (Wf.biUnion L).card ≤ (E ∩ Finset.range k).card + Wf.card := by
  intro k
  induction k with
  | zero =>
    intro _
    choose S hS1 hS2 using hin
    refine ⟨fun j => if h : j < 7 then S ⟨j, h⟩ else ∅, ?_, ?_⟩
    · intro j hj
      have hj7 : j < 7 := by omega
      simp only [dif_pos hj7]
      have : hw gs j = fun x => x ⟨j, hj7⟩ := by
        funext x; exact hw_input gs ⟨j, hj7⟩ x
      rw [this]; exact hS2 _
    · intro Wf hWf
      refine le_trans Finset.card_biUnion_le ?_
      have : ∑ j ∈ Wf, (if h : j < 7 then S ⟨j, h⟩ else ∅).card ≤ ∑ _j ∈ Wf, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj7 : j < 7 := by have := hWf j hj; omega
        simp only [dif_pos hj7]; exact hS1 _
      simpa using this
  | succ k ih =>
    intro hk
    obtain ⟨L, hL1, hL2⟩ := ih (by omega)
    have hklt : k < gs.length := by omega
    have hgk : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklt
    have hfank : gs[k].inputs.length ≤ 2 := hfan _ (List.getElem_mem hklt)
    -- a support for the new wire
    have key : ∃ Snew : Finset ι, Det D Φ Snew (hw gs (7 + k)) ∧
        ∀ Wf : Finset ℕ, (∀ j ∈ Wf, j < 7 + k) →
          (Snew ∪ Wf.biUnion L).card ≤ (E ∩ Finset.range (k + 1)).card + Wf.card + 1 := by
      -- reading a set R of earlier wires
      have viaR : ∀ (R : Finset ℕ) (c : ℕ), (∀ a ∈ R, a < 7 + k) → R.card ≤ c →
          (E ∩ Finset.range k).card + c ≤ (E ∩ Finset.range (k + 1)).card + 1 →
          Det D Φ (R.biUnion L) (hw gs (7 + k)) →
          ∃ Snew : Finset ι, Det D Φ Snew (hw gs (7 + k)) ∧
            ∀ Wf : Finset ℕ, (∀ j ∈ Wf, j < 7 + k) →
              (Snew ∪ Wf.biUnion L).card
                ≤ (E ∩ Finset.range (k + 1)).card + Wf.card + 1 := by
        intro R c hR hRc hc hdet
        refine ⟨R.biUnion L, hdet, ?_⟩
        intro Wf hWf
        rw [← Finset.union_biUnion]
        have h1 := hL2 (R ∪ Wf) (by
          intro j hj
          rcases Finset.mem_union.1 hj with h | h
          · exact hR j h
          · exact hWf j h)
        have h2 : (R ∪ Wf).card ≤ R.card + Wf.card := Finset.card_union_le _ _
        omega
      by_cases hkE : k ∈ E
      · -- an expensive gate: read all its inputs
        refine viaR (gs[k].inputs.toFinset.filter (· < 7 + k)) 2 ?_ ?_ ?_ ?_
        · intro a ha; exact (Finset.mem_filter.1 ha).2
        · exact le_trans (Finset.card_filter_le _ _)
            (le_trans (List.toFinset_card_le _) hfank)
        · rw [card_inter_range_succ k hkE]
        · intro x y hx hy hxy
          rw [hw_gate gs k _ x hgk, hw_gate gs k _ y hgk]
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases hak : a < 7 + k
          · rw [if_pos hak, if_pos hak]
            apply hL1 a hak x y hx hy
            intro s hs
            apply hxy
            exact Finset.mem_biUnion.2
              ⟨a, Finset.mem_filter.2 ⟨List.mem_toFinset.2 ha, hak⟩, hs⟩
          · rw [if_neg hak, if_neg hak]
      · rcases hE k _ hgk hkE with hnot | ⟨S, hS1, hS2⟩
        · -- a NOT gate reads its first input only
          have hev : ∀ x, hw gs (7 + k) x
              = !((gs[k].inputs.map fun a => if a < 7 + k then hw gs a x else false).headD
                  false) := by
            intro x
            rw [hw_gate gs k _ x hgk, hnot]
            rfl
          have hmono := card_inter_range_le (E := E) k
          cases hinp : gs[k].inputs with
          | nil =>
            refine viaR ∅ 1 (by simp) (by simp) (by omega) ?_
            intro x y _ _ _
            rw [hev x, hev y, hinp]
            rfl
          | cons a rest =>
            by_cases hak : a < 7 + k
            · refine viaR {a} 1 (by simpa using hak) (by simp) (by omega) ?_
              intro x y hx hy hxy
              rw [hev x, hev y, hinp]
              simp only [List.map_cons, List.headD_cons, if_pos hak]
              congr 1
              apply hL1 a hak x y hx hy
              intro s hs
              exact hxy s (by simpa using hs)
            · refine viaR ∅ 1 (by simp) (by simp) (by omega) ?_
              intro x y _ _ _
              rw [hev x, hev y, hinp]
              simp only [List.map_cons, List.headD_cons, if_neg hak]
        · refine ⟨S, hS2, ?_⟩
          intro Wf hWf
          have h1 := hL2 Wf hWf
          have h2 : (S ∪ Wf.biUnion L).card ≤ S.card + (Wf.biUnion L).card :=
            Finset.card_union_le _ _
          have hmono := card_inter_range_le (E := E) k
          omega
    obtain ⟨Snew, hS1, hS2⟩ := key
    refine ⟨Function.update L (7 + k) Snew, ?_, ?_⟩
    · intro j hj
      by_cases hjk : j = 7 + k
      · subst hjk; rw [Function.update_self]; exact hS1
      · rw [Function.update_of_ne hjk]; exact hL1 j (by omega)
    · intro Wf hWf
      by_cases hmem : 7 + k ∈ Wf
      · have hsub : Wf.biUnion (Function.update L (7 + k) Snew)
            ⊆ Snew ∪ (Wf.erase (7 + k)).biUnion L := by
          intro s hs
          obtain ⟨j, hj, hsj⟩ := Finset.mem_biUnion.1 hs
          by_cases hjk : j = 7 + k
          · subst hjk
            rw [Function.update_self] at hsj
            exact Finset.mem_union_left _ hsj
          · rw [Function.update_of_ne hjk] at hsj
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨j, Finset.mem_erase.2 ⟨hjk, hj⟩, hsj⟩)
        have h1 := Finset.card_le_card hsub
        have h2 := hS2 (Wf.erase (7 + k)) (by
          intro j hj
          have := hWf j (Finset.mem_of_mem_erase hj)
          have := Finset.ne_of_mem_erase hj
          omega)
        have h3 : (Wf.erase (7 + k)).card + 1 = Wf.card := Finset.card_erase_add_one hmem
        omega
      · have heq : Wf.biUnion (Function.update L (7 + k) Snew) = Wf.biUnion L := by
          apply Finset.biUnion_congr rfl
          intro j hj
          have : j ≠ 7 + k := fun h => hmem (h ▸ hj)
          rw [Function.update_of_ne this]
        rw [heq]
        have h1 := hL2 Wf (by
          intro j hj
          have := hWf j hj
          have : j ≠ 7 + k := fun h => hmem (h ▸ hj)
          omega)
        have hmono := card_inter_range_le (E := E) k
        omega

-- The concrete side: the edge function in closed form and its test inputs.
def fc (x : Fin 7 → Bool) : Bool :=
  (x 5 && (x 0 || x 1 || x 2 || x 3)) || (x 6 && (x 0 || x 1 || x 2 || x 3 || x 4 || x 5))

def wt (i j u : Fin 7) (c1 c2 c3 c4 : Bool) (p : Bool × Bool) : Fin 7 → Bool :=
  fun k => if k = i then p.1 else if k = j then p.2 else if k = u then c1
    else if k = 4 then c2 else if k = 5 then c3 else if k = 6 then c4 else false

def bl : List Bool := [false, true]

def pts : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

def sepB (i j u : Fin 7) (p q : Bool × Bool) : Bool :=
  bl.any fun c1 => bl.any fun c2 => bl.any fun c3 => bl.any fun c4 =>
    fc (wt i j u c1 c2 c3 c4 p) != fc (wt i j u c1 c2 c3 c4 q)

def sepOK (i j u : Fin 7) : Bool :=
  pts.any fun p => pts.any fun q => pts.any fun r =>
    sepB i j u p q && sepB i j u q r && sepB i j u p r

set_option maxRecDepth 100000 in
theorem sep_all : ∀ i j u : Fin 7, i ≠ j → u.val < 4 → ¬(i.val < 4 ∧ j.val < 4) →
    sepOK i j u = true := by decide

set_option maxRecDepth 100000 in
theorem dep_all : ∀ k u : Fin 7, u.val < 4 →
    sepB k k u (false, false) (true, true) = true := by decide

theorem sepB_spec {i j u : Fin 7} {p q : Bool × Bool} (h : sepB i j u p q = true) :
    ∃ c1 c2 c3 c4, fc (wt i j u c1 c2 c3 c4 p) ≠ fc (wt i j u c1 c2 c3 c4 q) := by
  simp only [sepB, List.any_eq_true, bne_iff_ne] at h
  obtain ⟨c1, -, c2, -, c3, -, c4, -, h⟩ := h
  exact ⟨c1, c2, c3, c4, h⟩

def proj (i : Fin 7) (x : Fin 7 → Bool) : Bool := x i

def DZ (Z : Finset (Fin 7)) (x : Fin 7 → Bool) : Prop := ∀ z ∈ Z, x z = false

def Smp (Z : Finset (Fin 7)) (h : (Fin 7 → Bool) → Bool) : Prop :=
  ∃ S : Finset (Fin 7), S.card ≤ 1 ∧ Det (DZ Z) proj S h

theorem wt_mem {Z : Finset (Fin 7)} (hZ : ∀ z ∈ Z, z.val < 4) {i j u : Fin 7}
    (hi : i ∉ Z) (hj : j ∉ Z) (hu : u ∉ Z) (c1 c2 c3 c4 : Bool) (p : Bool × Bool) :
    DZ Z (wt i j u c1 c2 c3 c4 p) := by
  intro z hz
  have h4 := hZ z hz
  have h1 : z ≠ i := fun h => hi (h ▸ hz)
  have h2 : z ≠ j := fun h => hj (h ▸ hz)
  have h3 : z ≠ u := fun h => hu (h ▸ hz)
  have h5 : z ≠ 4 := fun h => by rw [h] at h4; revert h4; decide
  have h6 : z ≠ 5 := fun h => by rw [h] at h4; revert h4; decide
  have h7 : z ≠ 6 := fun h => by rw [h] at h4; revert h4; decide
  simp [wt, h1, h2, h3, h5, h6, h7]

theorem wt_off (i j u : Fin 7) (c1 c2 c3 c4 : Bool) (p q : Bool × Bool) (k : Fin 7)
    (hi : k ≠ i) (hj : k ≠ j) :
    wt i j u c1 c2 c3 c4 p k = wt i j u c1 c2 c3 c4 q k := by
  simp [wt, hi, hj]

theorem wt_fst (i j u : Fin 7) (c1 c2 c3 c4 : Bool) (p : Bool × Bool) :
    wt i j u c1 c2 c3 c4 p i = p.1 := by
  simp [wt]

theorem wt_snd (i j u : Fin 7) (c1 c2 c3 c4 : Bool) (p : Bool × Bool) (hij : i ≠ j) :
    wt i j u c1 c2 c3 c4 p j = p.2 := by
  simp [wt, Ne.symm hij]

-- The expensive gates on the subcube where the coordinates in Z are false.
open Classical in
noncomputable def EZ (gs : List Gate) (Z : Finset (Fin 7)) : Finset ℕ :=
  (Finset.range gs.length).filter fun k =>
    ∃ g, gs[k]? = some g ∧ g.op ≠ GateOp.not ∧ ¬ Smp Z (hw gs (7 + k))

theorem EZ_spec (gs : List Gate) (Z : Finset (Fin 7)) (k : ℕ) (g : Gate)
    (hg : gs[k]? = some g) (hk : k ∉ EZ gs Z) :
    g.op = GateOp.not ∨ ∃ S : Finset (Fin 7), S.card ≤ 1 ∧ Det (DZ Z) proj S (hw gs (7 + k)) := by
  classical
  by_contra hcon
  push_neg at hcon
  apply hk
  have hlt : k < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    simp at hg
  simp only [EZ, Finset.mem_filter, Finset.mem_range]
  refine ⟨hlt, g, hg, hcon.1, ?_⟩
  rintro ⟨S, hS1, hS2⟩
  exact hcon.2 S hS1 hS2

theorem proj_simple (Z : Finset (Fin 7)) (j : Fin 7) :
    ∃ S : Finset (Fin 7), S.card ≤ 1 ∧ Det (DZ Z) proj S (fun x => x j) :=
  ⟨{j}, by simp, fun x y _ _ h => h j (by simp)⟩

-- Every wire is fixed by few coordinates.
theorem wire_det (gs : List Gate) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) (Z : Finset (Fin 7))
    (k : ℕ) (hk : k ≤ gs.length) (j : ℕ) (hj : j < 7 + k) :
    ∃ S : Finset (Fin 7), S.card ≤ (EZ gs Z ∩ Finset.range k).card + 1 ∧
      Det (DZ Z) proj S (hw gs j) := by
  obtain ⟨L, hL1, hL2⟩ := count_inv (DZ Z) proj gs hfan (proj_simple Z) (EZ gs Z)
    (EZ_spec gs Z) k hk
  refine ⟨L j, ?_, hL1 j hj⟩
  have := hL2 {j} (by simpa using hj)
  simpa using this

theorem main_bound (gs : List Gate) (o : ℕ) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hf : ∀ x, hw gs o x = fc x) :
    ∀ (n : ℕ) (Z : Finset (Fin 7)), Z.card + n = 7 → (∀ z ∈ Z, z.val < 4) →
      (∃ u : Fin 7, u.val < 4 ∧ u ∉ Z) → 7 ≤ (EZ gs Z).card + Z.card := by
  classical
  intro n
  induction n with
  | zero =>
    intro Z hc _ hu
    obtain ⟨u, _, hu⟩ := hu
    have : Z = Finset.univ := Finset.eq_univ_of_card Z (by simpa using hc)
    exact absurd (this ▸ Finset.mem_univ u) hu
  | succ n ih =>
    intro Z hc hZ hu
    obtain ⟨u, hu4, huZ⟩ := hu
    by_contra hlt
    have hlt : (EZ gs Z).card + Z.card ≤ 6 := by omega
    have hEsub : EZ gs Z ⊆ Finset.range gs.length := by
      intro k hk
      simp only [EZ, Finset.mem_filter] at hk
      exact hk.1
    -- the dependence of the edge function on every free coordinate
    have hdep : ∀ k : Fin 7, k ∉ Z → ∃ x y, DZ Z x ∧ DZ Z y ∧ fc x ≠ fc y ∧
        ∀ m : Fin 7, m ≠ k → x m = y m := by
      intro k hk
      obtain ⟨c1, c2, c3, c4, h⟩ := sepB_spec (dep_all k u hu4)
      exact ⟨_, _, wt_mem hZ hk hk huZ c1 c2 c3 c4 _, wt_mem hZ hk hk huZ c1 c2 c3 c4 _, h,
        fun m hm => wt_off k k u c1 c2 c3 c4 _ _ m hm hm⟩
    -- the output wire
    have hout : ∃ S : Finset (Fin 7), S.card ≤ (EZ gs Z).card + 1 ∧ Det (DZ Z) proj S fc := by
      have hfeq : hw gs o = fc := funext hf
      by_cases ho : o < 7 + gs.length
      · obtain ⟨S, hS1, hS2⟩ := wire_det gs hfan Z gs.length le_rfl o ho
        refine ⟨S, le_trans hS1 ?_, hfeq ▸ hS2⟩
        exact Nat.add_le_add_right (Finset.card_le_card Finset.inter_subset_left) 1
      · refine ⟨∅, by simp, ?_⟩
        intro x y _ _ _
        rw [← hf x, ← hf y, hw_big gs o x (by omega), hw_big gs o y (by omega)]
    obtain ⟨S, hS1, hS2⟩ := hout
    have hVS : Finset.univ \ Z ⊆ S := by
      intro k hk
      have hkZ : k ∉ Z := (Finset.mem_sdiff.1 hk).2
      by_contra hkS
      obtain ⟨x, y, hx, hy, hne, hag⟩ := hdep k hkZ
      exact hne (hS2 x y hx hy (fun s hs => hag s (fun h => hkS (h ▸ hs))))
    have hVcard : (Finset.univ \ Z).card = 7 - Z.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ Z)]; simp
    have hScard := Finset.card_le_card hVS
    have hEcard : (EZ gs Z).card + Z.card = 6 := by omega
    have hZ3 : Z.card ≤ 6 := by omega
    have hEne : (EZ gs Z).Nonempty := by
      rw [← Finset.card_pos]
      have : Z.card ≤ 3 := by
        have hsub : Z ⊆ (Finset.univ.filter fun z : Fin 7 => z.val < 4).erase u := by
          intro z hz
          exact Finset.mem_erase.2 ⟨fun h => huZ (h ▸ hz), by simpa using hZ z hz⟩
        have h1 := Finset.card_le_card hsub
        have h2 : ((Finset.univ.filter fun z : Fin 7 => z.val < 4).erase u).card = 3 := by
          rw [Finset.card_erase_of_mem (by simpa using hu4)]
          decide
        omega
      omega
    -- the first expensive gate
    set G := (EZ gs Z).min' hEne with hGdef
    have hGE : G ∈ EZ gs Z := Finset.min'_mem _ _
    have hGlt : G < gs.length := Finset.mem_range.1 (hEsub hGE)
    have hGfirst : EZ gs Z ∩ Finset.range (G + 1) = {G} := by
      ext a
      simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        have := Finset.min'_le _ a h1
        omega
      · rintro rfl
        exact ⟨hGE, by omega⟩
    obtain ⟨T, hT1, hT2⟩ := wire_det gs hfan Z (G + 1) (by omega) (7 + G) (by omega)
    rw [hGfirst] at hT1
    have hT1 : T.card ≤ 2 := by simpa using hT1
    -- the gate as one more feature
    let Φ' : Option (Fin 7) → (Fin 7 → Bool) → Bool := fun s =>
      match s with
      | none => hw gs (7 + G)
      | some i => proj i
    have hin' : ∀ j : Fin 7, ∃ S : Finset (Option (Fin 7)), S.card ≤ 1 ∧
        Det (DZ Z) Φ' S (fun x => x j) := by
      intro j
      exact ⟨{some j}, by simp, fun x y _ _ h => h (some j) (by simp)⟩
    have hE' : ∀ k g, gs[k]? = some g → k ∉ (EZ gs Z).erase G →
        g.op = GateOp.not ∨ ∃ S : Finset (Option (Fin 7)), S.card ≤ 1 ∧
          Det (DZ Z) Φ' S (hw gs (7 + k)) := by
      intro k g hg hk
      by_cases hkG : k = G
      · subst hkG
        exact Or.inr ⟨{none}, by simp, fun x y _ _ h => h none (by simp)⟩
      · have hkE : k ∉ EZ gs Z := fun h => hk (Finset.mem_erase.2 ⟨hkG, h⟩)
        rcases EZ_spec gs Z k g hg hkE with h | ⟨S, hS1, hS2⟩
        · exact Or.inl h
        · refine Or.inr ⟨S.map Function.Embedding.some, by simpa using hS1, ?_⟩
          intro x y hx hy h
          apply hS2 x y hx hy
          intro s hs
          exact h (some s) (by simp [hs])
    obtain ⟨L', hL1', hL2'⟩ := count_inv (DZ Z) Φ' gs hfan hin' ((EZ gs Z).erase G) hE'
      gs.length le_rfl
    have hout' : ∃ S' : Finset (Option (Fin 7)), S'.card ≤ (EZ gs Z).card ∧
        Det (DZ Z) Φ' S' fc := by
      have hfeq : hw gs o = fc := funext hf
      by_cases ho : o < 7 + gs.length
      · refine ⟨L' o, ?_, hfeq ▸ hL1' o ho⟩
        have h1 := hL2' {o} (by simpa using ho)
        have h2 : ((EZ gs Z).erase G ∩ Finset.range gs.length).card
            ≤ ((EZ gs Z).erase G).card := Finset.card_le_card Finset.inter_subset_left
        have h3 : ((EZ gs Z).erase G).card + 1 = (EZ gs Z).card :=
          Finset.card_erase_add_one hGE
        simp only [Finset.singleton_biUnion, Finset.card_singleton] at h1
        omega
      · refine ⟨∅, by simp, ?_⟩
        intro x y _ _ _
        rw [← hf x, ← hf y, hw_big gs o x (by omega), hw_big gs o y (by omega)]
    obtain ⟨S', hS1', hS2'⟩ := hout'
    -- the free coordinates outside T all lie in S'
    have hfree : ∀ k : Fin 7, k ∉ Z → k ∉ T → some k ∈ S' := by
      intro k hkZ hkT
      by_contra hkS
      obtain ⟨x, y, hx, hy, hne, hag⟩ := hdep k hkZ
      apply hne
      apply hS2' x y hx hy
      intro s hs
      cases s with
      | none => exact hT2 x y hx hy (fun t ht => hag t (fun h => hkT (h ▸ ht)))
      | some m => exact hag m (fun h => hkS (h ▸ hs))
    have hnone : none ∈ S' := by
      by_contra hno
      have hsub : (Finset.univ \ Z).map Function.Embedding.some ⊆ S' := by
        intro s hs
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hs
        have hkZ : k ∉ Z := (Finset.mem_sdiff.1 hk).2
        by_contra hkS
        obtain ⟨x, y, hx, hy, hne, hag⟩ := hdep k hkZ
        apply hne
        apply hS2' x y hx hy
        intro s hs
        cases s with
        | none => exact absurd hs hno
        | some m => exact hag m (fun h => hkS (h ▸ hs))
      have := Finset.card_le_card hsub
      rw [Finset.card_map] at this
      omega
    have hsub2 : ((Finset.univ \ Z) \ T).map Function.Embedding.some ⊆ S'.erase none := by
      intro s hs
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hs
      obtain ⟨hk1, hkT⟩ := Finset.mem_sdiff.1 hk
      exact Finset.mem_erase.2 ⟨by simp, hfree k (Finset.mem_sdiff.1 hk1).2 hkT⟩
    have hc2 := Finset.card_le_card hsub2
    rw [Finset.card_map] at hc2
    have hc3 : (S'.erase none).card + 1 = S'.card := Finset.card_erase_add_one hnone
    have hc4 : ((Finset.univ \ Z) \ T).card + ((Finset.univ \ Z) ∩ T).card
        = (Finset.univ \ Z).card := Finset.card_sdiff_add_card_inter _ _
    have hc5 : ((Finset.univ \ Z) ∩ T).card ≤ T.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hTV : (Finset.univ \ Z) ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have hT2c : T.card = 2 := by omega
    obtain ⟨i, j, hij, hTij⟩ := Finset.card_eq_two.1 hT2c
    have hiT : i ∈ T := by rw [hTij]; simp
    have hjT : j ∈ T := by rw [hTij]; simp
    have hiZ : i ∉ Z := by
      have : i ∈ (Finset.univ \ Z) ∩ T := by rw [hTV]; exact hiT
      exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 this).1).2
    have hjZ : j ∉ Z := by
      have : j ∈ (Finset.univ \ Z) ∩ T := by rw [hTV]; exact hjT
      exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 this).1).2
    have hSeq : ((Finset.univ \ Z) \ T).map Function.Embedding.some = S'.erase none :=
      Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_map]; omega)
    -- the edge function sees coordinates i and j only through the gate
    have htwin : ∀ x y, DZ Z x → DZ Z y → hw gs (7 + G) x = hw gs (7 + G) y →
        (∀ m : Fin 7, m ≠ i → m ≠ j → x m = y m) → fc x = fc y := by
      intro x y hx hy hg hag
      apply hS2' x y hx hy
      intro s hs
      cases s with
      | none => exact hg
      | some m =>
        have : some m ∈ S'.erase none := Finset.mem_erase.2 ⟨by simp, hs⟩
        rw [← hSeq] at this
        obtain ⟨k, hk, hkm⟩ := Finset.mem_map.1 this
        have hkm : k = m := by simpa using hkm
        subst hkm
        have hkT : k ∉ T := (Finset.mem_sdiff.1 hk).2
        rw [hTij] at hkT
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkT
        exact hag k hkT.1 hkT.2
    -- so both lie among the first four coordinates
    have hij4 : i.val < 4 ∧ j.val < 4 := by
      by_contra hbad
      have hs := sep_all i j u hij hu4 hbad
      simp only [sepOK, List.any_eq_true, Bool.and_eq_true] at hs
      obtain ⟨p, -, q, -, r, -, ⟨hpq, hqr⟩, hpr⟩ := hs
      have hsep : ∀ p q : Bool × Bool, sepB i j u p q = true →
          hw gs (7 + G) (wt i j u false false false false p)
            ≠ hw gs (7 + G) (wt i j u false false false false q) := by
        intro p q hpq hgeq
        obtain ⟨c1, c2, c3, c4, hne⟩ := sepB_spec hpq
        apply hne
        have hmove : ∀ p : Bool × Bool, hw gs (7 + G) (wt i j u c1 c2 c3 c4 p)
            = hw gs (7 + G) (wt i j u false false false false p) := by
          intro p
          apply hT2 _ _ (wt_mem hZ hiZ hjZ huZ _ _ _ _ _) (wt_mem hZ hiZ hjZ huZ _ _ _ _ _)
          intro s hs
          rw [hTij] at hs
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · simp only [proj]; rw [wt_fst, wt_fst]
          · simp only [proj]; rw [wt_snd _ _ _ _ _ _ _ _ hij, wt_snd _ _ _ _ _ _ _ _ hij]
        apply htwin _ _ (wt_mem hZ hiZ hjZ huZ _ _ _ _ _) (wt_mem hZ hiZ hjZ huZ _ _ _ _ _)
        · rw [hmove p, hmove q]; exact hgeq
        · intro m hmi hmj
          exact wt_off i j u c1 c2 c3 c4 p q m hmi hmj
      have h1 := hsep p q hpq
      have h2 := hsep q r hqr
      have h3 := hsep p r hpr
      revert h1 h2 h3
      generalize hw gs (7 + G) (wt i j u false false false false p) = a
      generalize hw gs (7 + G) (wt i j u false false false false q) = b
      generalize hw gs (7 + G) (wt i j u false false false false r) = c
      cases a <;> cases b <;> cases c <;> simp
    -- restrict coordinate j as well
    have hZ' : ∀ z ∈ insert j Z, z.val < 4 := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hij4.2
      · exact hZ z hz
    have hcard' : (insert j Z).card = Z.card + 1 := Finset.card_insert_of_notMem hjZ
    have hsmp : ∀ h, Smp Z h → Smp (insert j Z) h := by
      rintro h ⟨S, hS1, hS2⟩
      exact ⟨S, hS1, fun x y hx hy hxy =>
        hS2 x y (fun z hz => hx z (Finset.mem_insert_of_mem hz))
          (fun z hz => hy z (Finset.mem_insert_of_mem hz)) hxy⟩
    have hEsub' : EZ gs (insert j Z) ⊆ (EZ gs Z).erase G := by
      intro k hk
      simp only [EZ, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hklt, g, hg, hop, hns⟩ := hk
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl
        apply hns
        refine ⟨{i}, by simp, ?_⟩
        intro x y hx hy hxy
        apply hT2 x y (fun z hz => hx z (Finset.mem_insert_of_mem hz))
          (fun z hz => hy z (Finset.mem_insert_of_mem hz))
        intro s hs
        rw [hTij] at hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact hxy _ (by simp)
        · simp only [proj]
          rw [hx _ (Finset.mem_insert_self _ _), hy _ (Finset.mem_insert_self _ _)]
      · simp only [EZ, Finset.mem_filter, Finset.mem_range]
        exact ⟨hklt, g, hg, hop, fun h => hns (hsmp _ h)⟩
    have hc6 := Finset.card_le_card hEsub'
    have hc7 : ((EZ gs Z).erase G).card + 1 = (EZ gs Z).card := Finset.card_erase_add_one hGE
    have hih := ih (insert j Z) (by omega) hZ'
      ⟨i, hij4.1, by
        intro h
        rcases Finset.mem_insert.1 h with h | h
        · exact hij h
        · exact hiZ h⟩
    omega

theorem spec_bool : ∀ a b c d e f g : Bool,
    decide (∃ i < ([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (([a, b, c, d, e, f, g] : List Bool)).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (([a, b, c, d, e, f, g] : List Bool)).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
      = ((f && (a || b || c || d)) || (g && (a || b || c || d || e || f))) := by
  decide

theorem ofFn_seven (x : Fin 7 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

theorem spec_fc (x : Fin 7 → Bool) :
    decide (∃ i < ([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = fc x := by
  rw [ofFn_seven]
  exact spec_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def mono8 : List Gate :=
  [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [5, 6]⟩,
   ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [11, 13]⟩]

theorem mono8_bool : ∀ a b c d e f g : Bool,
    Circuit.eval ⟨mono8, 14⟩ [a, b, c, d, e, f, g]
      = ((f && (a || b || c || d)) || (g && (a || b || c || d || e || f))) := by
  decide

theorem mono8_fc (x : Fin 7 → Bool) : Circuit.eval ⟨mono8, 14⟩ (List.ofFn x) = fc x := by
  rw [ofFn_seven]
  exact mono8_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

theorem mono8_ops : ∀ g ∈ mono8,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono8, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem short_has_no_not (gates : List Gate) (o : ℕ)
    (hfan : ∀ g ∈ gates, g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = fc x)
    (hlen : gates.length ≤ 7) : ∀ g ∈ gates, g.op ≠ GateOp.not := by
  classical
  intro g0 hg0 hop0
  obtain ⟨k0, hk0, hgk0⟩ := List.getElem_of_mem hg0
  have hb := main_bound gates o hfan (fun x => hf x) 7 ∅ (by simp) (by simp)
    ⟨0, by decide, by simp⟩
  have hsub : EZ gates ∅ ⊆ (Finset.range gates.length).erase k0 := by
    intro k hk
    simp only [EZ, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hklt, g, hg, hop, -⟩ := hk
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 hklt⟩
    rintro rfl
    rw [List.getElem?_eq_getElem hk0, hgk0] at hg
    have : g0 = g := by simpa using hg
    exact hop (this ▸ hop0)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_range.2 hk0), Finset.card_range] at h1
  simp only [Finset.card_empty] at hb
  omega

end PEqualNP.Outside.L_meta_11817

theorem PEqualNP.Outside.L_meta_11817 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hops _ hf
  have hf' : ∀ x : Fin 7 → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x)
        = PEqualNP.Outside.L_meta_11817.fc x := by
    intro x
    rw [← PEqualNP.Outside.L_meta_11817.spec_fc x]
    exact hf x
  by_cases hlen : 8 ≤ gates.length
  · refine ⟨PEqualNP.Outside.L_meta_11817.mono8, 14,
      PEqualNP.Outside.L_meta_11817.mono8_ops, hlen, ?_⟩
    intro x
    rw [PEqualNP.Outside.L_meta_11817.spec_fc x]
    exact PEqualNP.Outside.L_meta_11817.mono8_fc x
  · have hno := PEqualNP.Outside.L_meta_11817.short_has_no_not gates o
      (fun g hg => (hops g hg).2) hf' (by omega)
    refine ⟨gates, o, ?_, le_rfl, hf⟩
    intro g hg
    obtain ⟨h, hl⟩ := hops g hg
    rcases h with h | h | h
    · exact ⟨Or.inl h, hl⟩
    · exact ⟨Or.inr h, hl⟩
    · exact absurd h (hno g hg)
