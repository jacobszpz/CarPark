// Manages a Car Park
class {:autocontracts} CarPark {
    // Total spaces
    const MAX_CAPACITY: int

    // Max reserved spaces
    const RESERVED_SPACES: int

    // Minimum spaces left in general area
    const MIN_SPACES_LEFT: int

    // Reserved area is open to general public
    var reservedOpen: bool

    // Cars registered for the reserved area
    var subscribed: set<int>

    // Car park total area
    var park: set<int>

    // Reserved spots taken
    var reserved: set<int>

    /**
     * Construct an empty CarPark with the limits specified
     */
    constructor(maxSpaces: int, maxReserved: int, minSpacesLeft: int)
        requires (minSpacesLeft + maxReserved) <= maxSpaces
    {
        MAX_CAPACITY := maxSpaces;
        RESERVED_SPACES := maxReserved;
        MIN_SPACES_LEFT := minSpacesLeft;

        reservedOpen := false;
        subscribed := {};

        park := {};
        reserved := {};
    }

    /**
     * Object Invariant
     */
    predicate valid()
    {
        // No more spaces taken than possible
        MAX_CAPACITY >= (MIN_SPACES_LEFT + |park|) &&
        // No more reserved spaces than possible
        MAX_CAPACITY >= RESERVED_SPACES &&
        // No more subscriptions than reserved spaces
        |subscribed| <= RESERVED_SPACES &&
        // No more reserved than subscribed
        |reserved| <= |subscribed|
    }

    /**
     * If there are spaces left to subscribe
     */
    predicate canSubscribe() {
        |subscribed| < RESERVED_SPACES
    }

    /**
     * Whether the general parking area is considered 'full'
     */
    predicate free() {
        (reservedOpen && ((MAX_CAPACITY - MIN_SPACES_LEFT - |park|) > 0)) ||
        (!reservedOpen && ((
                MAX_CAPACITY - MIN_SPACES_LEFT - RESERVED_SPACES
                - (|park| - |reserved|)) > 0))
    }

    /**
     * Allocates a car in the general area of the car park
     * @param car The ID of the car to put in the car park
     *
     * The car is guaranteed to be in the park if there is
     * space available
     */
    method enterCarPark(car: int) returns (success: bool)
        requires true;

        // If space was free, state should have changed*
        ensures old(free()) ==> (park == old(park) + {car});
        // Ensure car is in park if successful
        ensures success ==> car in park;
        modifies `park;
    {
        success := free() || car in park;

         // Allocate car in spaces left if not there already
         if (success)
         {
            park := park + {car};
         }
    }

    /**
     * Allow any car from any area to leave the car park
     * @param car The ID of the car to remove from the car park
     *
     * The car is guaranteed to not be in the park after calling
     */
    method leaveCarPark(car: int)
        requires true;
        // Car was removed from park and reserved section
        ensures park == old(park) - {car};
        ensures reserved == old(reserved) - {car};
        modifies `park, `reserved;
    {
        // Remove car from park
        park := park - {car};
        // Remove car from reserved list if in it
        reserved := reserved - {car};
    }

    /**
     * Report on the number of non-reserved free spaces currently available.
     */
    method checkAvailability() returns (available: int)
        requires true;
        // Result must be equal to the total capacity minus the reserved spaces
        // minus the currently used general spaces
        ensures !reservedOpen ==>
            (available == (MAX_CAPACITY - RESERVED_SPACES - (|park| - |reserved|)));
        // When the reserved area is open, the available spaces
        // are calculated without regarding it.
        ensures reservedOpen ==> (available == MAX_CAPACITY - |park|);
    {
        if (reservedOpen) {
            available := (MAX_CAPACITY - |park|);
        } else {
            available := (MAX_CAPACITY - RESERVED_SPACES - (|park| - |reserved|));
        }
    }

    /**
     * Allow a car with a subscription to enter the car park’s reserved area
     * on a weekday, or to enter the car park generally on a weekend day.
     * If the car is already in the car park, it will simply be 'moved'
     * to the reserved area.
     * The caller must ensure that the car is subscribed to parking.
     * Size does not need to be checked since we know that the subscriptions
     * are less or equal to the size of the reserved area.
     * @param car The ID of the car to put in the reserved area.
     */
    method enterReservedCarPark(car: int) returns (success: bool)
        requires car in subscribed || reservedOpen;

        // Park was only changed accordingly
        ensures !reservedOpen ==> (park == old(park) + {car});
        ensures !reservedOpen ==> (reserved == old(reserved) + {car});

        // Otherwise enterCarPark is called (cant express in postcondition afaik)
        modifies `park, `reserved;
    {
        // In weekends treat space as general car park
        if (reservedOpen) {
            var result := enterCarPark(car);
            return result;
        }

        // Add car to park, reserved in
        park := park + {car};
        reserved := reserved + {car};
    }

    predicate reservedAvailable() {
        |subscribed| < RESERVED_SPACES
    }

    /**
     * Allow a car to be registered as having a reserved space when
     * the owner pays the subscription – as long as subscriptions are available.
     * Returns true if car is subscribed, regardless of when it happened.
     */
    method makeSubscription(car: int) returns (success: bool)
        ensures old(canSubscribe()) ==> (subscribed == old(subscribed) + {car});
        ensures !(old(canSubscribe())) ==> (subscribed == old(subscribed));
        ensures success == (car in subscribed);
        modifies `subscribed;
    {
        success := canSubscribe() || car in subscribed;

        if (success)
        {
            subscribed := subscribed + {car};
        }
    }

    /**
     * Remove parking restrictions on the reserved spaces (at the weekend)
     */
    method openReservedArea()
        requires true;
        ensures reservedOpen && reserved == {};
        modifies `reservedOpen, `reserved;
    {
        reservedOpen := true;
        // Clear record of reserved clients who are in
        reserved := {};
    }

    /**
     * Remove and crush remaining parked cars at closing time
     * Subscriptions remain the same.
     */
    method closeCarPark()
        requires true;
        // Crush parked cars
        ensures park == {} && reserved == {} && !reservedOpen;
        // Preserve state
        modifies `park, `reserved, `reservedOpen;
    {
        park := {};
        reserved := {};
        reservedOpen := false;
    }

    method printParkingPlan()
    {
        // TODO: Implement parking plan
        print "Car Park: ";
        print park;
        print " Reserved In: ";
        print reserved;
        print "\n";

        print "Subscribed: ";
        print subscribed;
        print "\n";

        print "Total: ";
        print |park|;
        print "\n";

        print "Spaces: ";
        print MAX_CAPACITY;
        print " Subscriptions: ";
        print RESERVED_SPACES;
        print " Min Spaces: ";
        print MIN_SPACES_LEFT;
        print "\n";
    }
}

method Main() {
    print "Test Case 1: Max Free General Spaces...";

    // Total, Reserved, Min Left
    var park := new CarPark(15, 5, 5);

    // Should only contain 5 cars
    var c1 := park.enterCarPark(101);
    var c2 := park.enterCarPark(102);
    var c3 := park.enterCarPark(103);
    var c4 := park.enterCarPark(104);
    var c5 := park.enterCarPark(105);
    expect c5;
    var c6 := park.enterCarPark(106);
    expect !c6;
    print "PASS";
    print "\n\n";
}
