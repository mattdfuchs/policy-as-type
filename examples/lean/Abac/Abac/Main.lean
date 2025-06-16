import Abac.Protocol
import Abac.Model
import Abac.Validation

open Protocol

-- Example users
def daddy : User :=
  { name := "Daddy", age := 40, parent := none }

def sender : User :=
  { name := "Sender", age := 13, parent := some daddy }

def youngSender : User :=
  { name := "YoungSender", age := 10, parent := some daddy }

-- Supporting data
def context : Context :=
  { name := "Context", timeOfDay := 10 }

def channel : Transport :=
  { name := "Channel", protocol := https }

def payload : ItemRequest :=
  { name := "Payload", videoName := "I'm PG 13", ageLimit := 13 }

def service : Service :=
  { name := "Foo", isApproved := true }

def service2 : Service :=
  { name := "Foo", isApproved := false }

-- Test calls
def tryOne := preCall context sender channel payload service
def tryTwo := preCall context youngSender channel payload service
def tryThree := preCall context daddy channel payload service

def runCheck (label : String) (result : Option Item) : IO Unit :=
  match result with
  | some item => IO.println s!"{label}: ✅ got {item.name} (age {item.ageLimit})"
  | none => IO.println s!"{label}: ❌ failed"

def runDebug (label : String) (c : Context) (u : User) (ch : Transport) (p : ItemRequest) (s : Service) : IO Unit := do
  IO.println s!"--- {label} ---"

  let ctx := checkContext c
  let snd := checkSender u p
  let chl := checkChannel ch
  let pld := constrainPayload p
  let srv := checkService s

  IO.println s!"Context:   {if ctx.isSome then "✓" else "✗"}"
  IO.println s!"Sender:    {if snd.isSome then "✓" else "✗"}"
  IO.println s!"Channel:   {if chl.isSome then "✓" else "✗"}"
  IO.println s!"Payload:   {if pld.isSome then "✓" else "✗"}"
  IO.println s!"Service:   {if srv.isSome then "✓" else "✗"}"

  match ctx, snd, chl, pld, srv with
  | some ctx, some snd, some chl, some pld, some srv =>
      match safeCall ctx snd chl pld srv with
      | some item =>
          IO.println s!"Result:    ✅ got {item.name} (age {item.ageLimit})"
      | none =>
          IO.println "Result:    ❌ safeCall failed"
  | _, _, _, _, _ =>
      IO.println "Result:    ❌ some precheck failed"

def run : IO Unit := do
  runDebug "tryOne" context sender channel payload service
  runDebug "tryTwo" context youngSender channel payload service
  runDebug "tryThree" context daddy channel payload service

#eval run
