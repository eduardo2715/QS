// Declaration of a set of people
sig Person {
  friends: set Person  // Each person can have a set of friends
}

// A fact to ensure that friendship is mutual
fact MutualFriendship {
  all p: Person | all f: p.friends | p in f.friends
}

// A predicate to check if someone has no friends 
pred NoFriends[p: Person] {
  no p.friends
}

// A predicate to check if someone has exactly one friend
pred OneFriend[p: Person] {
  one p.friends
}

// A sample assertion to verify mutual friendship
assert MutualFriendshipCheck {
  all p: Person | all f: p.friends | p in f.friends
}

// Command to check the assertion
check MutualFriendshipCheck

// Command to run a scenario with 3 people
run {} for 5 Person
