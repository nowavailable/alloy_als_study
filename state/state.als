open util/ordering[Time]

sig Event, Time {}
sig Transtion {
	target: State,
	evnet: Event
}
sig State {
	transtion: Event -> one Transtion
}
sig Component {
	state: State,
  stated: Time -> one State,
  evented: Time -> one Event
}
sig InterFace{}
run {} for 2 but 1 Component
