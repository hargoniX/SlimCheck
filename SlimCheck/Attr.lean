/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/
import Lean.Util.Trace

open Lean

initialize registerTraceClass `slim_check.instance
initialize registerTraceClass `slim_check.decoration
initialize registerTraceClass `slim_check.discarded
initialize registerTraceClass `slim_check.success
initialize registerTraceClass `slim_check.shrink.steps
initialize registerTraceClass `slim_check.shrink.candidates
