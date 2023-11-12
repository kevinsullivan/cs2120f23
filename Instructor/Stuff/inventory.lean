inductive Image | aPhoto

structure CatEntry : Type where
(id : Nat)        -- unique id
(name : String)
(desc : String)
(photo : Image)
(captn : String)
(paid value price sold: Nat)

inductive Item
| thing (cat : CatEntry)  : Item
| box   (cat: CatEntry) (items : List Item) : Item
-- different items should have different cat entries

def cat_entry : Item → CatEntry
| Item.thing cat => cat
| Item.box cat _ => cat

/-!
Use case. Late into sorting, starting catalog. Today
I recognized the opportunity to consolidate spatially
significant collections of networking things into one
place. I'll recursively merge, sort, and catalog the
stuff I have in a few places, including a section of
shelves opposite the workbench.

At the top level, I'll create a single new box to hold
the whole collection of things that come out, under the
main heading of networking equipment. We'll need a cat
entry to start.
-/

def network_equipment_cat : CatEntry := CatEntry.mk
1
"Network equipment"
"From routers, wifi, switches and cables to wifi hot
spots and line of site virtual ethernet hardware, to
include some exterior mounting hardware."
Image.aPhoto
"Network equipment spread out on workbench"
0 0 0 0

def wireless_ethernet_cat : CatEntry := CatEntry.mk
2
"Wireless Ethernet"
"Multiple componenets including mountings"
Image.aPhoto
"Wireless ethernet equipment"
0 0 0 0

def wireless_ethernet_transmitter_cat : CatEntry := CatEntry.mk
3
"Wireless ethernet transmitter"
"Unopened box"
Image.aPhoto
"Wireless transmitter"
0 0 0 0

def wireless_ethernet_transmitter : Item :=
Item.thing wireless_ethernet_transmitter_cat

def wireless_ethernet_equipment :=
Item.box wireless_ethernet_cat
[
  wireless_ethernet_transmitter
]

def network_equipment : Item := Item.box network_equipment_cat
[ wireless_ethernet_equipment,
  Item.box wireless_ethernet_cat [
    Item.thing wireless_ethernet_transmitter_cat
  ]
]
