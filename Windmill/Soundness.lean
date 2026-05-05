import Windmill.Certificate

namespace Windmill

theorem check_points_nontrivial {cert : Certificate} (h : check cert = true) :
    cert.points.size > 1 := by
  unfold check at h
  simp at h
  exact h.1.1.1

theorem check_general_position {cert : Certificate} (h : check cert = true) :
    generalPosition cert.points = true := by
  unfold check at h
  simp at h
  exact h.1.1.2

theorem check_cycle_closed {cert : Certificate} (h : check cert = true) :
    cycleClosed cert = true := by
  unfold check at h
  simp at h
  exact h.1.2

theorem cycle_closed_nonempty {cert : Certificate} (h : cycleClosed cert = true) :
    cert.cycle.size > 0 := by
  unfold cycleClosed at h
  simp at h
  exact h.1

theorem cycle_closed_edges {cert : Certificate} (h : cycleClosed cert = true) :
    ∀ i : Nat, i < cert.cycle.size →
      transitionValid
        cert.points
        cert.cycle[i]!
        cert.cycle[(i + 1) % cert.cycle.size]! = true := by
  unfold cycleClosed at h
  simp at h
  exact h.2

theorem check_cycle_edges {cert : Certificate} (h : check cert = true) :
    ∀ i : Nat, i < cert.cycle.size →
      transitionValid
        cert.points
        cert.cycle[i]!
        cert.cycle[(i + 1) % cert.cycle.size]! = true :=
  cycle_closed_edges (check_cycle_closed h)

theorem check_cover_valid {cert : Certificate} (h : check cert = true) :
    coverValid cert = true := by
  unfold check at h
  simp at h
  exact h.2

theorem cover_valid_size {cert : Certificate} (h : coverValid cert = true) :
    cert.cover.size = cert.points.size := by
  unfold coverValid at h
  simp at h
  exact h.1

theorem cover_valid_covers {cert : Certificate} (h : coverValid cert = true) :
    ∀ i : Fin cert.points.size,
      ∃ j : Fin cert.cycle.size, (cert.cycle[j]).curr = i.val := by
  intro i
  unfold coverValid at h
  simp at h
  have hall := h.2 i.val (by exact i.isLt)
  simp at hall
  let j : Fin cert.cycle.size := ⟨cert.cover[i.val]!, hall.1⟩
  refine ⟨j, ?_⟩
  change (cert.cycle[cert.cover[i.val]!]'hall.1).curr = i.val
  have hget :
      cert.cycle[cert.cover[i.val]!]! =
        cert.cycle[cert.cover[i.val]!]'hall.1 :=
    getElem!_pos cert.cycle (cert.cover[i.val]!) hall.1
  rw [← hget]
  exact hall.2

theorem check_covers {cert : Certificate} (h : check cert = true) :
    ∀ i : Fin cert.points.size,
      ∃ j : Fin cert.cycle.size, (cert.cycle[j]).curr = i.val :=
  cover_valid_covers (check_cover_valid h)

end Windmill
