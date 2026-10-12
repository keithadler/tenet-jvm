In `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` (current master) there are six pairs of lemmas with identical statements and proofs:

- `le_rpow_of_log_le` / `rpow_le_of_le_log`
- `le_pow_of_log_le` / `pow_le_of_le_log`
- `le_zpow_of_log_le` / `zpow_le_of_le_log`
- `lt_rpow_of_log_lt` / `rpow_lt_of_lt_log`
- `lt_pow_of_log_lt` / `pow_lt_of_lt_log`
- `lt_zpow_of_log_lt` / `zpow_lt_of_lt_log`

They were added in #15859. By the file's naming convention, the second column should be the forward direction of `rpow_le_iff_le_log` / `rpow_lt_iff_lt_log` (e.g. `rpow_le_of_le_log : z * log x ≤ log y → x ^ z ≤ y`, mirroring `le_log_of_rpow_le`), but each one just restates its partner from the first column. So I think the statements are wrong rather than redundant, and the lemmas the names promise don't exist.

None of the second set is used anywhere else in Mathlib (the `pow_le_of_le_log` hits elsewhere are the `Nat` and `Ordinal` lemmas), so restating them with the intended statements should be a safe change. Happy to open a PR if that's the preferred fix; the alternative is deprecating them as aliases.

Found with my linter's duplicate-statement check (https://github.com/keithadler/lean-linter).
