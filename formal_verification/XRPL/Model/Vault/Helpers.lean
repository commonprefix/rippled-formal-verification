-- temporary fix to detect overflow exception on arithmetic operations.
-- todo: replace with actual exception handling
def isOverflow (s : String) : Bool := (s.splitOn "overflow").length ≥ 2
