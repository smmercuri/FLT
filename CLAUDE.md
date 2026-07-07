
# Speed diagnosis

You will investigate and diagnose issues with compilation time in certain files in FLT.

## Boss theorems

The boss theorems of this task are leaf-node theorems that must be invariant under your work.
By invariant, I mean that they should always compile and that their axiom list should always consist precisely of
`[propext, Classical.choice, Quot.sound]`.

Specifically, these are the following theorems:
- `NumberField.AdeleRing.cocompact`
- `NumberField.AdeleRing.discrete`

## Task: speed diagnosis

Your task is to diagnose issues with compilation time in a sub-tree of the FLT project.
The files in consideration are detailed in `.cache/flt_import_closure.txt` and
`.cache/flt_import_closure_output.json`.

You MUST follow the process outlined in the following flowchart.
Before every action you MUST state which phase of the flowchart you are in using,
for example, `[CURRENT STATE: TIME]`.

```mermaid
graph TD
    START((Start Task)) --> TIME[Time all files]
    TIME --> PROFILE[Profile declarations]
    PROFILE --> TRACE[Get trace reports]
    TRACE --> REPORT[Produce final report]
    REPORT --> LOG[Record to log]
    LOG --> STOP((Stop Task))
```

### 📋 Process State Definitions

| State | Definition & Action | Success Criteria (Gate) |
| :--- | :--- | :--- |
| **TIME** | Run the `flt_profile_ranking` tool to get file-level compilation times. | A ranked list of the most expensive files with respect to compilation time. |
| **PROFILE** | For each of the top offending files call the `profile_file` tool to get per-decl compilation statisticts. | A ranked list of the most expensive decls in each of the most expensive files as output by the previous step |
| **TRACE** | Use the `analyze_synth_trace` tool and the `analyze_isdefeq_trace` tool on the list of declarations output by the previous step. | Trace outputs and individual reports for each of the top declarations. |
| **REPORT** | Create a single global report containing common issues across the trace reports; provide recommendations for a future agent to fix. | Singular report containing description of the key issues and recommendations; it should be detailed enough for a future agent to action your recommendations. |
| **LOG** | Use the `record_log` tool to record your actions and findings in `.cache/log.jsonl` | -- |
| **STOP** | -- | -- |

- **CRITICAL**: The number of top files/decls to focus on is 5.
- **CRITICAL**: When calling timing tools make sure they are saved to an "before" subdirectory of the pass in .cache.
- **CRITICAL**: Your final report should try to identify commonalities amongst the issues found in the top 25 final declarations.
- **CRITICAL**: Your final report should also identify potential conflicts amongst the issues found in the top 25 final declarations. For example, if one proposed fix could cause degradation in other areas then this must be flagged.
- **CRITICAL**: Your final report should provide a priority ordering of the proposed fixes. This should take into account their overall ranking in the compilation time, but also the likelihood that it may cause conflicts for other areas to fix.

## Task: speed fixing

Your task here is to make fixes as recommended by the latest speed diagnosis.

You MUST follow the process outlined in the following flowchart.
Before every action you MUST state which phase of the flowchart you are in using,
for example, `[CURRENT STATE: TIME]`.

```mermaid
graph TD
    START((Start Task)) --> FIX[Make fixes]
    FIX --> FIX_DEPENDENT[Fix dependent files]
    FIX_DEPENDENT --> CHECK_BOSS[Verify boss theorems]
    CHECK_BOSS -- Pass --> TIME_FIX[Time after fixes]
    CHECK_BOSS -- Fail --> FIX
    TIME_FIX --> REPORT[Write improvement report]
    REPORT --> LOG[Record to log]
    LOG --> STOP((Stop Task))
```

### 📋 Process State Definitions

| State | Definition & Action | Success Criteria (Gate) |
| :--- | :--- | :--- |
| **FIX** | Make the fixes recommended by the diagnosis. Follow the priority ordering. Use `lean-lsp-mcp` tools to interact with the Lean environment | Isolated files compile without errors. |
| **FIX_DEPENDENT** | Continue fixing dependent modules until the 64 modules compile without errors. | All targeted files compile without error. |
| **CHECK_BOSS** | Verify that the boss theorems still compile and that they are axiom-clean. | If axiom-clean then move on to TIME_FIX, else return to FIX to resolve the issue |
| **TIME_FIX** | Use `profile_file` to time the flagged files and decls that you have fixed, and use `flt_build_timing` to time the overall build. You do not need to time files that have been fixed as dependents. | Files and decls flagged by the diagnosis timed, and overall project build timed.  |
| **REPORT** | Create a single report comparing the timings after fixes and before. | -- |
| **LOG** | Use the `record_log` tool to record your actions and findings in `.cache/log.jsonl` | -- |
| **STOP** | -- | -- |

- **CRITICAL**: When calling timing tools make sure they are saved to an "after" subdirectory of the pass in .cache.
- **CRITICAL**: Do not make any fixes that are flagged by the diagnosis for mathlib.
- **CRITICAL**: Avoid making changes that improve one area at the cost of another, as flagged by the diagnosis.
