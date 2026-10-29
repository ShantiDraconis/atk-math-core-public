namespace ATK.Audit
/-- Auditoria: `TerminalGate C` habitado ⟺ `C`. -/
theorem gate_iff (C : Prop) : Nonempty (ATK.TerminalGate C) ↔ C :=
  ⟨fun ⟨g⟩ => g.close, fun c => ⟨⟨True, True.intro, fun _ => c⟩⟩⟩
end ATK.Audit
