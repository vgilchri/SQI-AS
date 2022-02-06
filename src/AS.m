
load "src/sqisign.m";

// discrete logarithm fn
// Y = nX, return n
find_log := function(X, Y);
	n:= 1;
	repeat
		Z:= n*X;
		n:= n+1;
	until (Z eq Y) or (n eq 5^4);
	return n-1;
	"loop done";
	n;
end function;

monty_scalar_mult := function(n,P);
	counter := 2;
	M:=P`curve;
	answer:= XAdd(P,P,ZeroXZ(M));
	repeat
		answer := XAdd(P,answer,P);
		counter := counter + 1;
	until counter eq n;
	return answer;
end function;

monty_subtract:=function(P,Q);
	M:=Montgomery(P`curve,Parent(P`X)!1);
	P_A := Lift(P,M);
	x1:= P_A`x;
	y1:= P_A`y;
	z1:= P_A`z;
	if (z1 ne 1) and (z1 ne 0) then
		x1 := x1 / z1;
		y1 := y1 / z1;
	end if;
	Q_A := Lift(Q,M);
	x2:= Q_A`x;
	y2:= Q_A`y;
	z2:= Q_A`z;
	if (z2 ne 1) and (z2 ne 1) then 
		x2 := x2 / z2;
		y2 := y2 / z2;
	end if;
	y2:= -1*y2;
	B:= M`B;
	A:= M`A;
	x3:=(B*(y2-y1)^2) / (x2-x1)^2 - A - x1 - x2;
	y3:= ((2*x1 + x2 + A)*(y2 - y1) / (x2 - x1)) - (B*(y2-y1)^3 / (x2-x1)^3) -y1;
	x3:= x3 / y3;
	z3:= 1 / y3;
	return SemiMontgomeryXZ(x3,z3,P`curve);
end function;

// hard problem KeyGen / all KeyGen
// generates: [y, (E_Y, P_Y, Q_Y, pi_Y)]
// define degree sizes
deg_bound:=120;
wit_deg:=5^16;
// to find basis points for statement
basis_of_power_of_5_torsion := function(E);
	M:=SemiMontgomery(E);
	n := 16;
	// n := 21;
	cofactor:=(p+1) div 5^(n+1);
	repeat
		B1 := cofactor*Random(M);
		B12n:=B1*5^(n);
	until not IsIdentity(B12n) and IsIdentity(B12n*5);
	repeat
		B2 := cofactor*Random(M);
		B22n:=B2*5^(n);
	until (not IsIdentity(B22n) and IsIdentity(B22n*5)) and (not (B12n eq B22n));
	return [M!(5*B1),M!(5*B2)];
end function;

// generate statement, witness pair and torsion basis points
sqias_witness_gen:=function()
	B<i,j,k>:=Parent(Basis(O0)[1]);

	n := exponent_power_of_2_rational_torsion;

	T := available_odd_torsion;
	T2 := T^2;
	fT2 := Factorisation(T2);
	cof:=(p+1) div 5^16;
	cof_twist:=(p-1) div 3^53;
	M:=SemiMontgomery(E0);
	repeat
		ker:=RandomXZ(M,true)*cof;
		ker5:=5^15*ker;
	until IsIdentity(5*ker5) and not IsIdentity(ker5);
	repeat
		ker_twist:=RandomXZ(M,false)*cof_twist;
		ker3_twist:=3^52*ker_twist;
	until IsIdentity(3*ker3_twist) and not IsIdentity(ker3_twist);
	gen:=<<ker,5^16,[<5,16>] >,<ker_twist,3^53,[<3,53>]> >;
	assert <IsIdentity(gene[2]*gene[1]): gene in gen> eq <true,true>;
	wit:=list_kernel_generators_to_isogeny(gen);
	statement:=codomain(wit[#wit]);
	// gen0:=<<eval_isogenies(gene[1],phi_commit_dual),gene[2]> : gene in gen>;
	//assert <IsIdentity(gene[2]*gene[1]): gene in gen0> eq <true,true>;
	// assert Norm(H) eq Norm(H1)*Norm(H2);
	basis5:=basis_of_power_of_5_torsion(statement);
	return wit,statement,basis5[1],basis5[2];
end function;

sqias_witness_gen2:=function()
	base_curve:=SemiMontgomery(E0);
	basis5:=basis_of_power_of_5_torsion(base_curve);
	P_Y :=basis5[1];
	Q_Y := basis5[2];
	"basis done";
	secret:=Random(5^4);
	"secret int is";
	secret;
	temp:=secret*Q_Y;
	"secret times Q_Y is";
	temp;
	PQ_Y:=monty_subtract(P_Y,temp);
	wit_ker:=XAdd(P_Y , temp, PQ_Y);
	"kernel from witness_gen is";
	wit_ker;
	ell:= 5^8;
	degree_bound:= 5^21;
	wit:=Isogeny(wit_ker, ell, degree_bound);
	statement:= codomain(wit);
	return wit, statement, P_Y, Q_Y;
end function; 

// generate commitment with E_Y hash
sqi_gen_commitment_odd:=function(E_Y)
	M1 := Matrix([[1,0],[0,1]]);
	M:=SemiMontgomery(E0);
	cof:= GCD([p+1,available_odd_torsion]) div (5^21);
	cof_twist:= GCD( [(p-1),available_odd_torsion]) div (3^53);
	ker:=ZeroPt(E0);
	ker_orth:=ZeroPt(E0);
	ker_twist:=ZeroPt(E0_twist);
	ker_orth_twist:=ZeroPt(E0_twist);
	H:=lideal<O0|1>;
	for i in [1..#basis] do
		L:=torsion_data[i][1];
		e:=torsion_data[i][2];
		if L ne 5 then
			if i ne #basis then
				if L ne torsion_data[i+1][1] then
					torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
					P:=basis_Le[1];
					Q:=basis_Le[2];
					M2 := action_dist_Le;
					M3_double := (M1 + action_distfrob_Le);
					M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
					M4_double := (action_dist_Le + action_frob_Le);
					M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
					kerL:=P+Random(1,L)*Q;
					ker:=ker+kerL;
					ker_orth:=ker_orth+Q;
					H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
				end if;
			else
				torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
				P:=basis_Le[1];
				Q:=basis_Le[2];
				M2 := action_dist_Le;
				M3_double := (M1 + action_distfrob_Le);
				M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
				M4_double := (action_dist_Le + action_frob_Le);
				M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
				kerL:=P+Random(1,L)*Q;
				ker:=ker+kerL;
				ker_orth:=ker_orth+Q;
				H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
			end if;
		end if;
	end for;
	monty_coef :=Integers()!Norm(E_Y`A);
	statement_seed:= monty_coef mod (2^(32) - 1);
	SetSeed(statement_seed);
	h:= Random(100000); // not sure how large need to make this...check against a cryptographic hash
	SetSeed(h);
	for i in [1..#basis_twist] do
		L:=torsion_data_twist[i][1];
		e:=torsion_data_twist[i][2];
		if L ne 3 then
			if i ne #basis_twist then
				if L ne torsion_data_twist[i+1][1] then
					torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
					P:=basis_Le[1];
					Q:=basis_Le[2];
					M2 := action_dist_Le;
					M3_double := (M1 + action_distfrob_Le);
					M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
					M4_double := (action_dist_Le + action_frob_Le);
					M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
					kerL:=P+Random(1,L)*Q;
					ker_twist:=ker_twist+kerL;
					ker_orth_twist:=ker_orth_twist+Q;
					H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
				end if;
			else
				torsion_data_Le, basis_Le, action_dist_Le, action_frob_Le, action_distfrob_Le, frobenius_twisters_Le, m := get_torsion_data(L^e);
				P:=basis_Le[1];
				Q:=basis_Le[2];
				M2 := action_dist_Le;
				M3_double := (M1 + action_distfrob_Le);
				M3 := ChangeRing(ChangeRing(M3_double,Integers(L^e))/2,Integers());
				M4_double := (action_dist_Le + action_frob_Le);
				M4 := ChangeRing(ChangeRing(M4_double,Integers(L^e))/2,Integers());
				kerL:=P+Random(1,L)*Q;
				ker_twist:=ker_twist+kerL;
				ker_orth_twist:=ker_orth_twist+Q;
				H:=H meet kernel_to_ideal_from_action(O0,L,e,kerL,P,Q,M1,M2,M3,M4);
			end if;
		end if;
	end for;
	gen_commit:=< <Project(ker),cof,Factorization(cof),Project(ker_orth)>,<Project(ker_twist),cof_twist,Factorization(cof_twist),Project(ker_orth_twist)> >;
	phi_commit:=list_kernel_generators_to_isogeny(gen_commit);
	phi_dual:=dual_odd_isogeny(phi_commit,gen_commit);
	commitment:=codomain(phi_commit[#phi_commit]);
	return commitment,phi_commit,phi_dual,H,P,Q;
end function;

// presign: (tau, message, E_Y) --> (presig, tau(P_Y), tau(Q_Y))
// start with sqisign
// extend commitment to depend on E_Y
presign := function(sk,pk,K,phi_K,isom_K,J,phi_J,epsilon, E_Y, P_Y, Q_Y)
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;
	// signing_odd_torsion:=3^53*5^21; //should not be bigger than p/N
	signing_odd_torsion:=1;

	message := [Random(1,2^32-1),Random(1,2^64-1) ];
		//generate  challenge + commitment
		t:=ClockCycles();
		commitment,phi_commit,phi_commit_dual,I_commit:=sqi_gen_commitment_odd(E_Y);
		commit_time:=timediff(t);
		tt:=ClockCycles();
		phi_chall,chall,H_chall:=gen_honest_challenge_prover(phi_commit_dual,I_commit,message);
		challenge_time :=timediff(tt);

		//generate the signature ideal
		tt:=ClockCycles();
		equivalent_ideal:=small_equivalent_ideal(Conjugate(sk)*H_chall);
		_,alpha:=LeftIsomorphism(J,sk);
		sign_ideal:=QuaternionIsogenyPath_special_Extended2(order,w1,w2,equivalent_ideal,sk,2:addit_factor:=signing_odd_torsion);
		sign_ideal:=cyclic_ideal(sign_ideal:full:=true);
		klpt_time:=timediff(tt);
		sign_ideal:=sign_ideal*lideal<RightOrder(sign_ideal)|Conjugate(alpha)/Norm(alpha)>;
		sign_ideal:=rideal<LeftOrder(sign_ideal)|alpha>*sign_ideal;

		//computing the signature isogeny
		tt:=ClockCycles();
		presign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon:other_side_isogeny:=phi_commit cat phi_chall,other_side_ideal:=H_chall);
		 // sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(J*sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon);
		 translate_time:=timediff(tt);
		//normalizing and compressing
		walk, zip, last_step,len:=normalized_two_walk(presign_isogeny,sign_isom);
		sign_time:=timediff(t);


		//computing the verification
		tt:=ClockCycles();
		ver:=verify(commitment,message,zip,pk,len,last_step);
		assert(ver);
		if not ver then "problem with the verification"; end if;
		verif_time:=timediff(tt);
		
		tau_P := Evaluate(phi_K[1], [P_Y])[1];
		tau_Q := Evaluate(phi_K[1], [Q_Y])[1];
		tau_deg:= phi_K[1]`degree;
		counter:=2;
		"# of isos";
		#phi_K;
		repeat
			"counter is";
			counter;
			"deg is";
			phi_K[counter]`degree;
			M:=Montgomery(tau_P`curve,Parent(tau_P`X)!1);
			P_A := Lift(tau_P,M);
			tau_P:=Evaluate(phi_K[counter], [tau_P])[1];
			tau_Q:=Evaluate(phi_K[counter], [tau_Q])[1];
			tau_deg*:=phi_K[counter]`degree;
			counter+:=1;
		until counter eq (#phi_K);
	return commit_time,challenge_time,klpt_time,translate_time,sign_time,verif_time,Valuation(Z!Norm(sign_ideal),2), tau_P, tau_Q, presign_isogeny,tau_deg;
end function;


// adapt: (presig_iso, y, P_Y, Q_Y, tau_P, tau_Q) --> (sig, pi_y2)
adapt:=function(presign_isogeny,y,P_Y, Q_Y, tau_P, tau_Q, tau_deg);
// run sidh to get E_yA
	// get y kernel generator <-- K
	K:=y`isogeny`kernel_points[1];
	"kernel called in adapt is";
	K;
	// discrete log of K in terms of P_Y, Q_Y <-- s
	KP_Y:=monty_subtract(K,(-1*P_Y));
	//"KP_Y sub done";
	S:= XAdd(K, (-1*P_Y), KP_Y);
	//S:= monty_subtract(K, P_Y);
	"here is K - P_Y";
	S;
	s:=find_log(Q_Y, S);
	"secret int is";
	s;
	// tau_P + s tau_Q <-- K'
	temp:=s*tau_Q;
	tau_PQ:= monty_subtract(tau_P,temp);
	K2 := XAdd(tau_P, temp, tau_PQ);
	// iso(K2) <-- y'
	y2_deg:=tau_deg * y`degree;
	y2:=Isogeny(K2,y2_deg,deg_bound);
// run sidh on presig and y' 
	// compose kernel generator using s
	K_R:=Evaluate(presign_isogeny, K2);
	// define iso
	sig_deg:=presign_isogeny`degree * y2_deg;
	sig:=Isogeny(K_R,sig_deg,deg_bound);
	return sig;
end function;


// extract: (presign_isogeny, sig, P_Y, Q_Y, tau_P, tau_Q) --> (y)
extract:=function(presign_isogeny,sig,P_Y,Q_Y,tau_P,tau_Q);
	// find kernel generator of sig 
	K_R := sig`isogeny`kernel_points[1];
	// compute presig hat
	presig_hat:=DualIsogeny(presign_isogeny);
	// run sidh on sig and presig hat
	K_Y:=Evaluate(presig_hat,K_R);
	// obtain secret int s
	tau_KP:=monty_subtract(K_Y, (-1*tau_P));
	R_Y:= XAdd(K_Y,(-1*tau_P),tau_KP);
	s:=find_log(tau_Q, R_Y);
	"secret recovered in extract is";
	s;
	// define witness with new kernel
	temp := s*Q_Y;
	PQ_Y:=monty_subtract(P_Y,temp);
	S:=XAdd(P_Y, temp,PQ_Y);
	"ker after extracting is";
	S;
	y:=Isogeny(S, wit_deg,deg_bound);
	return y;
end function;



Test_sqias:=procedure()
	"testing SQI-AS";
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;
	epsilon:=14;
	number_batch:=1;
	number_round:=1;
	sign_times:=[];
	klpt_times:=[];
	commit_times:=[];
	challenge_times:=[];
	translate_times:=[];
	gen_times:=[];
	times_not_sorted:=[];
	sizes:=[];
	verif_times:=[];
	"about to gen keys";
	//generate the key

		//"\n Test_sqisign \n number of batches:",number_batch," number of rounds:",number_round," \n";
	//for index in [1..number_batch] do
		t:=ClockCycles();
		sk,pk,K,phi_K,isom_K,J,phi_J:=gen_keys();
		gen_time:=timediff(t);
		gen_times:=sort_insert(gen_times,gen_time);
		for ind in [1..number_round] do
			t:=ClockCycles();
			// domain(phi_K[#phi_K])
			"about to gen witness";
			wit, E_Y, P_Y, Q_Y:=sqias_witness_gen2();
			"witness gen done, starting presign";
			commit_time,challenge_time,klpt_time,translate_time,sign_time,verif_time,size,tau_P,tau_Q,presign_isogeny,tau_deg:=presign(sk,pk,K,phi_K,isom_K,J,phi_J,epsilon, E_Y,P_Y, Q_Y);
			"presign done, about to sign";
			sig:=adapt(presign_isogeny,wit,P_Y, Q_Y, tau_P, tau_Q, tau_deg);
			"sign done, about to extract";
			y:=extract(presign_isogeny,sig,P_Y,Q_Y,tau_P,tau_Q);
			"extracted witness is",y;
			"original witness is",wit;
			commit_times:=sort_insert(commit_times,commit_time);
			challenge_times:=sort_insert(challenge_times,challenge_time);
			klpt_times:=sort_insert(klpt_times,klpt_time);
			translate_times:=sort_insert(translate_times,translate_time);
			sign_times:=sort_insert(sign_times,sign_time);
			verif_times:=sort_insert(verif_times,verif_time);
			Append(~times_not_sorted,sign_time);
			Append(~sizes,size);
		end for;
	//end for;



	//"median generation time is is ",gen_times[#gen_times div 2 +1];
	//"median signing time for epsilon = ",epsilon," is ",sign_times[#sign_times div 2 +1];
	//"median verification time is", verif_times[#verif_times div 2+1];
	//"median commit time is", commit_times[#commit_times div 2+1];
	//"median challenge time is", challenge_times[#challenge_times div 2+1];
	//"median klpt time is", klpt_times[#klpt_times div 2+1];
	//"median translate time is", translate_times[#translate_times div 2+1];

	gen_times;
	sign_times;
	verif_times;
	sizes;
end procedure;

Test_sqias();
