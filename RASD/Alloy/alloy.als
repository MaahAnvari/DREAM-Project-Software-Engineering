sig Float{}
sig Email, Username, Password, Id{}
sig Integer{}
sig Str{}
sig Fertilizer{}
sig Status{}
one sig Active extends Status {}
one sig Closed extends Status {}
sig City{}
sig Region{
	city: some City
}
sig State{
	reg: some Region
}
sig Date	{
	timeStamp: one Integer
} 
sig Message{
	date: one Date,
	writer: one Farmer,
	content: one Str
}
sig Sensor{
	id: one Id,
	measur : one Float,
	location: one Location,
}

sig WaterIrr{
	id: one Id,
	measur: one Float,
	location: one Location,
}

sig Weather{
	date: one Float,
	temp: one Integer,
	location: one Location
}
sig Crop{
	name: Str,
	weight: Int
}
sig Location{
	state: one State,
	long: one Float,
	lat: one Float,
}
sig Discussion{
	topic: Str,
	participant: some Farmer,
	owner: one Farmer,
	status: Active,
	msg: some Message
}
sig Problem{
	topic: Str,
	participant: set Farmer,
	owner: one Farmer,
	status: Active,
	msg: set Message	
}
sig Farmland{
	farmer: one Farmer,
	crops: set Crop,
	fertilizers: set Fertilizer,
	location: one Location,
	humidity: one Float,
	water: one Float,
	weather: one Weather
}
sig Farmer{
	email: one Email,
	username: one Username,
	password: one Password,
	problems: some Problem,
	discussions: some Discussion,
	land: Farmland,
	rate: Int
}{ rate >0 and rate <=5}
sig PolicyMaker{
	username: one Username,
	email: one Email,	
	farmers: set Farmer,
	bestF: set Farmer,
	worstF: set Farmer
}{ worstF != bestF }
//////////////////////////////  FACT     ////////////////////////////
fact disEmail{
  no disj f1,f2: Farmer | f1.email = f2.email
}
fact disEmailP{
  no disj p1,p2: PolicyMaker | p1.email = p2.email
}
fact disUsername{
  no disj f1,f2: Farmer | f1.username = f2.username
}
fact DistinctWaterIrrigationSystems{
	no disj w1, w2: WaterIrr | w1.location = w2.location
}
fact DistinctMessagesDiscussion{
	no disj d1, d2: Discussion | d1.msg = d2.msg
}
fact DistinctMessagesProblem{
	no disj p1, p2: Problem | p1.msg = p2.msg
}

fact MappingHumidity{
	all fl: Farmland, s:Sensor |  fl.humidity = s.measur iff fl.location = s.location
}
fact MappingWater{
	all fl: Farmland, w:WaterIrr |  fl.water = w.measur iff fl.location = w.location
}
fact disjointIdS{
	no disj s1, s2: Sensor| s1.id = s2.id
}
fact disjointIdW{
	no disj w1, w2: WaterIrr| w1.id = w2.id
}
//Assign each farmeland to exacly one farmer
fact OneOwnerForDisscussion{
	all d: Discussion | one f: Farmer | d.owner = f
}
// Only Farmers can participate in a problem or discussions iff they are in participant list
fact OnlyParticipantCanParticipateInDiscussion{
	all f: Farmer | all d: Discussion| d in f.discussions implies f in d.participant
}
fact OnlyParticipantCanParticipateInProblem{
	all f: Farmer | all p: Problem| p in f.problems implies f in p.participant
}
// Writer should be part of participants
fact MappingParticipantToWriters{
	all p: Problem | one f:Farmer | f in p.msg.writer iff f in p.participant
}
fact MappingParticipantToDiscussion{
	all d: Discussion | one f:Farmer | f in d.msg.writer iff f in d.participant
}
fact BestFarmerInTheList{
	all p: PolicyMaker | all f: Farmer| f in p.bestF iff f in p.farmers
}
fact distinctWorstandBest{
	all p: PolicyMaker | p.worstF != p.bestF
}

fact SelectWorstFarmer{
	all p: PolicyMaker | all f: Farmer | p.worstF = f iff f.rate < 2
}
fact SelectWorstFarmer{
	all p: PolicyMaker | all f: Farmer | p.bestF = f iff f.rate > 4
}
//////////////////////////    Pred ///////////////////////////////////

//Create Farm Land
pred InitialInformation(fl: Farmland, f: Farmer, c: Crop, fr: Fertilizer, l: Location, h: Float, w: Float, wt: Weather) {
	fl.farmer = f
	fl.crops = fl.crops +c
	fl.fertilizers = fl.fertilizers + fr
	fl.location = l
	fl.weather = wt
	fl.water = w
}
run InitialInformation

// Start Discussion
pred CreateForumD(d: Discussion, f: Farmer, t: Str, m: Message){
	d.owner = f
	d.participant = d.participant + f
	d.topic = t
	d.msg = m
} 

run CreateForumD

//Ask Problem
pred CreateForumP(p: Problem, f: Farmer, t: Str, m: Message){
	p.owner = f
	p.participant = p.participant + f
	p.topic = t
	p.msg = m
} 

run CreateForumP

// Join to existing Problem
pred JoinForumP(p: Problem, f: Farmer, fo: Farmer, t: Str, m: Message){
	p.owner = fo
	p.participant = p.participant + f
	p.topic = t
	p.msg = m
} 
run JoinForumP

// Select Best and Worst Farmers by PolicyMakers
pred SelectBestFarmer(p: PolicyMaker, bf: Farmer, wf:Farmer, f: Farmer, u: Username, e:Email){
	p.username = u
	p.email = e
	p.bestF = bf
	p.worstF = wf
	p.farmers = f
} 

run SelectBestFarmer
