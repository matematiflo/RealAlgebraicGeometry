def main : IO Unit :=
  IO.println "Hello, world!"

#eval main

-- #eval IO.println "Hello, world!"

#eval 1 + 1

#check 3

def f (n : Nat) : Nat := 2 * n

#eval f 3

-- #print f