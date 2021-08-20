
load "src/sqisign.m";

// hard problem KeyGen / all KeyGen
// generates: [y, (E_Y, P_Y, Q_Y, pi_Y)]

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
	SetSeed(E_Y`A);
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
		sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon:other_side_isogeny:=phi_commit cat phi_chall,other_side_ideal:=H_chall);
		 // sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(J*sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon);
		 translate_time:=timediff(tt);
		//normalizing and compressing
		walk, zip, last_step,len:=normalized_two_walk(sign_isogeny,sign_isom);
		sign_time:=timediff(t);


		//computing the verification
		tt:=ClockCycles();
		ver:=verify(commitment,message,zip,pk,len,last_step);
		assert(ver);
		if not ver then "problem with the verification"; end if;
		verif_time:=timediff(tt);
		
		tao_P := Evaluate(phi_K, P_y);
		tao_Q := Evaluate(phi_K, Q_y);

	return commit_time,challenge_time,klpt_time,translate_time,sign_time,verif_time,Valuation(Z!Norm(sign_ideal),2), tau_P, tau_Q;
end function;


// adapt: (presig, y, P_Y, Q_Y, tau_P, tau_Q) --> (sig, pi_y2)
// run sidh to get E_yA
	// get y kernel generator <-- K
	K:=y`ker;
	// discrete log of K in terms of P_Y, Q_Y <-- s
	S:= K-P_Y;
	s:=Log(Q_Y, S);
	// tau_P + s tau_Q <-- K'
	K2 := tau_P+s*tau_Q;
	// iso(K2) <-- y'
	y2:=Isogeny(K2,deg,deg_bound);
	// y' dual
	y2_hat:=DualIsogeny(y2);
	
	// presig \circ y'_hat <-- sig
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;	
	equivalent_ideal:=small_equivalent_ideal(Conjugate(y2_ideal)*presig_ideal);
	_,alpha:=LeftIsomorphism(J,presig_ideal);
	sig_ideal:=QuaternionIsogenyPath_special_Extended2(order,w1,w2,equivalent_ideal,presig_ideal,2:addit_factor:=signing_odd_torsion);
	sig_ideal:=cyclic_ideal(sig_ideal:full:=true);
	sig_ideal:=sig_ideal*lideal<RightOrder(sign_ideal)|Conjugate(alpha)/Norm(alpha)>;
	sig_ideal:=rideal<LeftOrder(sig_ideal)|alpha>*sig_ideal;	
	// return KLPT(sig)


// extract: (presig, sig) --> (y)

// verify

end procedure;
