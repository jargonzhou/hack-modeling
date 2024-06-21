/---- MODULE Point ----
LOCAL INSTANCE Integers
CONSTANTS X, Y

ASSUME X \in Int
ASSUME Y \in Int

Point == <<X, Y>>
Add(x, y) == <<X + x, Y + y>>
====