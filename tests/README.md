# Repository tests

Run the complete suite with `make test`. For a focused run, use discovery so
shared helpers remain importable:

```bash
python3 -m unittest discover -s tests -p 'test_build_commands.py' -v
```

Keep tests beside the responsibility they check:

- `test_build_commands.py` checks build orchestration and Make dispatch;
- `test_format_commands.py` checks formatter behavior and source preservation;
- `test_source_commands.py` checks source gates and end-of-file normalization;
- `test_repository_commands.py` checks cleanup, environment inspection, and usage;
- `test_new_book.py` checks scaffold creation and rollback;
- `test_image_workflow.py` checks image selection and registry isolation;
- `test_snapshot_workflow.py` checks snapshot publication and Pages inputs;
- `test_workflow_contracts.py` checks workflow wiring and inline shell syntax.

The other modules cover their named Python modules, commands, or integrations.
Script-file syntax checks belong to `make check source`; inline workflow shell
syntax remains in the workflow tests. Keep unit and integration checks when they
exercise different boundaries rather than repeating the same assertion.

`test_support.py` provides fresh book records and manifest documents, YAML and
executable writers, an isolated Git environment, and process-group cleanup.
Use builders for valid setup data; keep intentionally invalid records and expected
results explicit in their tests. Register temporary-directory cleanup immediately.
Start long-lived subprocesses in new sessions and register process cleanup after
creation so it runs before directory cleanup. Bound subprocess waits with timeouts.

`workflow_support.py` reads the current build workflow and evaluates its explicit
boolean gate expressions. It supports comparisons, boolean operators, and the
`always()` and `cancelled()` functions used by these tests; it does not emulate
GitHub Actions job scheduling or implicit status checks.

Site contract tests check actual stylesheet links and accessibility rule presence.
They do not assert rendered layout or pin spacing values, selectors, or breakpoints.
Lean audit and LaTeX rendering tests require their corresponding toolchains and
report skips when their prerequisite executables are absent. LaTeX fixtures live
in `fixtures/`; build output stays under ignored `build/` directories.
