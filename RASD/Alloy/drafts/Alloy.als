abstract sig User {
read: some  TrafficViolationStatistics
}

sig EndUser extends User {
see: set Violation,
send: set ViolationData
}

sig Authority extends User {
see: set ViolationData,
position: Position,
notifications: set ViolationData,
warned: set ViolationData,
checked: set ViolationData,
code: GCode
}

sig Municipality extends User {
see: set UnsafeArea,
send: AccidentData,
code: GCode
}

sig Violation {
position: Position,
date: Date,
time:Time
}

sig ViolationData {
description: Description,
licensePlate: LicensePlate,
type: ViolationType,
date: Date,
time:Time,
position: Position
}

sig TrafficViolationStatistics {}

sig UnsafeArea {
position: Position,
interventions: set Intervention
}

sig Intervention {}

sig AccidentData {
date: Date,
time: Time,
position: Position
}

sig LicensePlate {}

sig Date {}

sig Time {}

sig ViolationType{}

sig Position {}

sig Description {}

sig GCode {}



-- FACTS
--1. a violation can belong to no more than one EndUser
fact {
no disj eu1, eu2: EndUser | 
        all v: ViolationData |
         ( v in eu1.send and  v in eu2.send)
}

--2. each violation has an EndUser who sent it
fact {
all v: ViolationData | 
  one eu: EndUser |
     v in eu.send
}

--3. all warned violations can't be in checked (for authority)
fact {
no a: Authority |
       one v: ViolationData | 
         ( v in a.checked and v in a.warned)
}

--3.5 all checked violations can't be in notifications (for authority)
fact {
no a: Authority |
       one v: ViolationData | 
         ( v in a.checked and v in a.notifications)
}

--4. a violation checked by an authority can't be checked by another one
fact {
all v: ViolationData |
  no disj a1, a2: Authority |
         ( v in a1.checked and v in a2.checked)
}

--5. a violation can't be at the same time warned and checked for the same 
--authority
fact {
all a: Authority |
  (a.warned & a. checked = none)
}
--alternativa
fact {
no v: ViolationData |
  one a: Authority |
    (v in a.warned and v in a.checked)
}

--6. a GCode can belong to only one authority and to only one municipality
fact {
no disj a1, a2: Authority |
    one gc: GCode |
       (gc in a1.code and gc in a2.code)
}
fact {
no disj m1, m2: Municipality |
    one gc: GCode |
       (gc in m1.code and gc in m2.code)
}
fact {
no a: Authority, m: Municipality |
    one gc: GCode |
       (gc in a.code and gc in m.code)
}

--7. each AccidentData has to be associated to one municipality
fact {
all ad: AccidentData |
  one m: Municipality |
    ad in m.send
}

--8. domain assumption: user sends violation from the position in which
-- the violation occurred
fact {
all vd: ViolationData | 
  one eu: EndUser, v: Violation | 
     (vd in eu.send ) implies
                ((v in eu.see) and 
                         vd.position=v.position and
   						vd.time=v.time and
							  vd.date=v.date)
}

--9. all ViolationData must be in all Authority.see
fact {
all vd: ViolationData, a: Authority |
 vd in a.see
}

--PREDICATES
--1. new violation sent by a user
pred sendViolation [eu, eu': EndUser, vd: ViolationData] {
}

--2. authority checks violation
pred checkViolation [a, a': Authority, vd: ViolationData] {
a'.checked = a.checked + vd
a'.notifications = a.notifications - vd
}

pred showcheckViolation [a, a' : Authority, vd: ViolationData] {
checkViolation [a, a', vd]
}

--ASSERTIONS
--1. all ViolationData that an authority sees must be in the send attribute 
-- of one user
assert AuthoritySeesEndUserViolations {
all vd: ViolationData |
  one a: Authority, eu: EndUser | 
     (vd in a.see) implies
			   (vd in eu.send)
}

--check AuthoritySeesEndUserViolations for 3





















