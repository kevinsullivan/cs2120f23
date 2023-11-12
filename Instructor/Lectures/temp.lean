/-!
concept is top super-interface for all concepts implemented as NP-style code bases
-/

/-!

- *code base* for a bonafide concept suitable for inclusion in a library
- a *app* has a type α, with associated metadata, such as [has_sequenceable α]
-/


-- concepts as types
axiom my_concept : Type

class has_flutter_project (α : Type)
-- has relative path to project directory 
-- has lib, packages, pubspec.yaml, etc

class has_min_app (α : Type) [has_flutter_project α]
-- has cloudformation templates
-- has open api specification
-- must have front end directory
-- has to have code_gen directory
-- constraints already expressed as assertions in concept_dir/atomic.py

-- two alternative ways to create data flows between sequentially composed apps 
class has_state_monad

class is_mediator_composable (α : Type)
-- lookup event bus 
-- and events on event bus
-- concept-specific action api (e.g., start, stop)
-- currently set up to call back-end and decide on return what events to post

class has_sequenceable (α : Type) [has_flutter_project α] [has_min_app α] [is_mediator_composable α]
-- broadcast start and end events
-- needs sequenceable inerface implementation, bloc has to extend (details needed)

-- let mediating components listen, react, call, get data, pass it on, etc
class has_state_interface
class has_actions_interface
class has_event_interface

 -- e.g., database 

class has_parameters_and_returns

class has_auth (α : Type) [has_flutter_project α] [has_min_app α] [has_sequenceable α]
-- cloudformation description of identity pool
-- more details ...
