-- data types
inductive Question : Type

structure Questionnaire where
  (l : List Question) 

variable
  (location_questionnaire : Questionnaire)
  (mdt_questionnaire : Questionnaire)
  (mmdhp_questionnaire : Questionnaire)
  
  
/- wrong  
  (location_response : Response)
  (mdt_response : Response)
  (mmdhp_response : Response)
-/

class Reporter where
( report : Result → Unit)

structure State where

class SequentiallyComposable where
(start : State → Unit)
(done : Unit)


structure Survey extends Reporter where
  -- state
  (e : Environment)
  (q : Questionnaire)
  (rs : List Response := [])

  -- ops (too ADT'y?)
  (fetch_questionnaire := q)
  (submit : Response → Unit := λ _ => Unit.unit)

  -- behavior process
  /-
    - wait for start
    - signal starting
    - output questionnaire to environment
    - get response input r from environment
    - store r in db
    - return r (done)
  -/

structure MDT_Survey extends Survey, Sequenceable, Reporter

structure Environment where
  (getInputFromEnv : Unit)
  (sendResultToEnv : Unit)

/-
What does survey interaction process need from 
its environment?
- get inputs from environment
- a place to send outputs 
- a way to send it signals 
-/


variable 
  (mdt_survey : Survey := { q := mdt_questionnaire })
  (mmdhp_survey : Survey := { q := mmdhp_questionnaire })
  (location_survey : Survey := { q := location_questionnaire })




/-!
A report is a list of sections. A section is a result.
-/

structure Report where
(reports : List Result)
(reporters : List CI [Reporter][Sequenceable])
(run : Unit)