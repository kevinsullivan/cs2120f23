structure Process
structure State
structure Communication

structure Agent
(pr : Process)
(st : State)
(cm : Communication)

structure Address
structure Mailbox

def a_proc := Process.mk
def a_state := State.mk
def a_comms := Communication.mk
def an_addr := Address.mk
def an_mailbox := Mailbox.mk
def an_agent : Agent a_proc a_state a_comms := Agent.mk

#check (Agent a_proc a_state a_comms)   -- this is a type of agent

def agent_address : (Agent a_proc a_state a_comms) → Address := sorry

/-!
Properties

- Everything is an actor
- 
-/