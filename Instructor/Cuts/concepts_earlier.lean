-- Some concepts (each with a single implciit constructor/value called mk)
structure Message   -- we will enable tagging
structure Video     -- we will enable tagging
structure Auth      -- cannot be tagged

/-!
Taggability of instances of type α means you can get 
or set a list of tags associated with any α instance.
-/
structure Tag

class Taggable (α : Type) where
(getTags : α → List Tag)        -- I/O
(setTags : α → List Tag → Unit) -- I/O

-- We enable taggability for Message and Video concepts but not for Auth
instance : Taggable Message :=  { 
                                  getTags := λ (m : Message) => _
                                  setTags := λ (m : Message) (tags : List Tag) => _
                                }
instance : Taggable Video :=    { 
                                  getTags := λ (v : Video) => _ 
                                  setTags := λ (v : Video) (tags : List Tag) => _
                                }

/-!
Now we can write polymorphic yet strongly and statically typed actions.
This function takes a target type (such as Message or Video) as long as
there's also an implementation of Taggable for that specific type, along
with a "target" instance, targ, of that taggable type (such as Message or 
Video). With all that in hand, it invokes the getTags operation for that
type of taggable instance to get its associated tags.
-/

def getTags {targType : Type} [Taggable targType] (targ : targType) : List Tag := 
  Taggable.getTags targ


/-!
Demo.

(1) Create instances of Message, Video, Auth, and Tag.
-/
def m := Message.mk
def v := Video.mk
def a := Auth.mk
def t := Tag.mk

/-!
We can now get the tags associated with a message or a
video but not from an auth instance.
-/
#check getTags m    -- returns tags on message m
#check getTags v    -- returns tags on video v 
#check getTags a    -- tagging not support for auth 
