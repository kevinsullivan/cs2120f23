universe u
structure Concept : Type where
(name : String := "")
(purpose : String := "")


/-!
-- Questionnaire data type and a few examples
-/
structure Question
structure Questionnaire where
(questions : List Question)

def locationQuestionnaire : Questionnaire := Questionnaire.mk []
def temperatureQuestionnaire : Questionnaire := Questionnaire.mk []
def contributorsQuestionnaire : Questionnaire := Questionnaire.mk []
-- def modQuestionnaire : Questionnaire := Questionnaire.comp [locationQuestionnaire, temperatureQuestionnaire, contruibutorsQuestionnaire]


/-!
Survey concept and some examples
-/
inductive Survey  -- CONCEPT (ALONG WITH OPERATIONS, EVENTS)
| elem (c : Concept := ⟨ "", "" ⟩) (q : Questionnaire) 
| comp (c : Concept := ⟨ "", "" ⟩) (l : List Survey)


/-!
-/
def locationSurvey := Survey.elem ⟨ "loc", "get loc info" ⟩ locationQuestionnaire  
def temperatureSurvey := Survey.elem ⟨ "temp", "get temp info" ⟩ temperatureQuestionnaire
def contributorsSurvey := Survey.elem ⟨ "contrib", "get contrib factors info" ⟩ contributorsQuestionnaire
def modSurvey := Survey.comp ⟨ "mod survey", "get 3-part survey result" ⟩ [locationSurvey, temperatureSurvey, contributorsSurvey]


/-!
Resiliency Resources (what is the generalized concept here, general, akin to survey)
-/
structure Followup :=
new :: (c : Concept)

def resiliencyResources := Followup.new ⟨ "", "" ⟩ 



/-!
MoD App
-/

structure MoDApp
(c : Concept := ⟨ "MoD App", "Take survey and provide followup" ⟩)
(modSurvey : Survey := modSurvey)
(followUp : Followup := resiliencyResources )

/-!
By policy we've synchronized "being a concept" with
"having a possibly parameterized full-stack codebase 
implementation." Moreover, "being a concept" concretel
means, in this design, holding a (unique) instance of 
type, Concept. Users should enforce uniqueness for now.

So, in the system we're defining here, MoDApp, will be
a concept type in our new ontology, so "noo ModApp", an
application of our build time "new" operator to MoDApp,
will build and deploy a new instance of this type, with  
-/