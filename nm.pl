use strict;

# For the NM QSO Party, 2009
#
# Based on Washington State Salmon Run scorer, 2008 Revision - 
#  
# Note that this DOES NOT cross-check QSO's between stations.
# this program reads the cabrillo or almost cabrill or or pseudo cabrillo file, 
# and generates a score according to some rules.
#  
# To use -- perl nm.pl <files_to_score>
#use warnings;
# process a qso party log
#
# verify zone list for a log file
#
# SCOREFILE -- scores are appended to this file in CSV format
my $SCOREFILE = "scores.csv";
my $logfile;
my $ZONELIST = "zonelist" ;
my $COUNTYLIST = "nm_cty" ;
my $CTFILE = "cty.dat";
my $STATESPROVS = "StatesAndProvinces.sec";
my $BONUS_STATION = 'N5M'; # uppercase please

# load the zone list
my %STZONE;
my %QPT;
my %DXCC_ENTITY;
my %COUNTY;
my %STATEPROV;
#
# What are the QSO types worth as far as points?
$QPT{"CW"}=2;
$QPT{"RY"}=2;
$QPT{"DG"}=2;
$QPT{"PS"}=2;
$QPT{"PH"}=1;

my %NORMALIZED_MODE = ( "CW" => "CW" , 
			"PH" => "PH" ,
			"DG" => "DG" ,
			"RY" => "DG" , 
			"RT" => "DG" , 
			"PS" => "DG" );
 ;
my @BONUS_STATION_BONUS_MODES=('CW','PH','DG');   # for what modes do we count BONUS_STATION bonus?

my $debug_level = 0;
my $debug_scoring = 1;
my @LOG;
my %FIELD_OFFSETS; # adjust worked call, received exchange, sent exch offsets of various logging programs

# These are all special-cases, derived from cabrillo logs found in-the-wild. When someone sends in a really whacky one,
# we sometimes replace the name of the logging program (the 'CREATED-BY') line with the call of the station, making a brand
# new unique format. 
# special cases for 2006 
$FIELD_OFFSETS{'N3FJP'}="53:9,67:5,44:6";   # there are a couple of different versions of this
$FIELD_OFFSETS{'N3RJ'}="56:14,74:6,50:5";
$FIELD_OFFSETS{'N7EIE'}="50:10,65:4,45:4";
$FIELD_OFFSETS{'KT7G'}="49:10,68:4,79:4";
$FIELD_OFFSETS{'K3ZT'}="48:10,61:5";
#

$FIELD_OFFSETS{'N1MM'}="55:14,73:10,48:6";
$FIELD_OFFSETS{'NA'}="54:13,71:7,47:6";
$FIELD_OFFSETS{'SD'}="55:14,72:7";
$FIELD_OFFSETS{'WRITELOG'}="65:14,83:5,48:6";
$FIELD_OFFSETS{'TR'}="55:14,69:17,46:6";
$FIELD_OFFSETS{'GENLOG'}="26:12,57:7,44:6";
$FIELD_OFFSETS{'VE5BF'}="59:9,73:5,50:6";
$FIELD_OFFSETS{'LOGEQF'}="55:12,73:5,48:6";
$FIELD_OFFSETS{'W5TD'}="53:10,70:4,48:6";


# 
# normalize the mode -- 
#
sub normalize_mode {
    my ($mode) =@_;
    my $normal_mode = 'UNKNOWN';
    # print ("MODE is [$mode]\n");
    $normal_mode = $NORMALIZED_MODE{$mode} if defined($NORMALIZED_MODE{$mode});
    return $normal_mode;
}
#
# score the log in the LOG variable -- don't verify, just score them
#
sub score_log {
	my $filename;
	($filename) = @_;
	my $calc_score;
    my %ISADUPE;
    my %SENT_EXCHANGE;
    my $LOGHEADER;
    my $wa_cnty;
	my $cnty_cnt = 0;
	my $dx_cnt = 0;
    my $dig_cnt = 0;
    my $cw_cnt = 0;
    my $ph_cnt = 0;
    my $idx = 0;
    my $total_q=0;
    my $is_wa = -1;
    my %cntymult;
    my %dxmult;
    my %statemult;
	my $mode; my $band;
    my %modeqcnt;
    my %BONUS; 
    my $bonus_pts = 0;
    my $iam = '';
    my $i; my $om; my $rexch; my $wrkd; my $dupeindex; 
    my $creator = '';
    my $qline;
    my %LOGHEADER;
    my $sect;
	my $totpoints;
    my $state_cnt;
    my $claimed_score; my $dupecnt;
    my $wrked_offset; my $wrked_len; my $exch_offset; my $exch_len; my $sent_offset; my $sent_len; 
	my $sexch;

    $idx = 0; $dupecnt=0;
	while ($idx < $#LOG) {
	  $qline = $LOG[$idx];

      if ($qline =~ /^([\w,-]+)\:\s*(.*)\s*/) {
		if (!($1 eq 'QSO')) { # don't save QSO info
		 # print $1," ",$2,"\n";
		if (defined($LOGHEADER{$1})) {
			  $LOGHEADER{$1} .= " ";
		}
	    $LOGHEADER{$1} .= $2;
	    }
	  }

   	  if (substr($qline,0,10) eq "CREATED-BY") {
		$creator = substr($qline,11);
	    $creator =~ s/(\w+).*/$1/;
	    $creator =~ s/\s//g;
		print "Log Creator is $creator\n";
		if (!defined($FIELD_OFFSETS{$creator})) {
			print("WARNING - Haven't seen a log created by $creator before -- trying N1MM defaults\n");
            $creator = "N1MM";
	    }
        ($wrked_offset,$wrked_len,$exch_offset,$exch_len,$sent_offset,$sent_len) = split(/[,:]/,$FIELD_OFFSETS{$creator})	;
	
	  }

   	  if (substr($qline,0,8) eq "CALLSIGN") {
		$iam = substr($qline,9);
	    $iam =~ s/\s//g;
		print "Callsign: $iam\n";
	  }

   	  if (substr($qline,0,13) eq "CLAIMED-SCORE") {
		$claimed_score = substr($qline,15);
	  }

   	  if (substr($qline,0,12) eq "ARRL-SECTION") {
		 $sect =substr($qline,14);
	     $sect =~ s/\s+// ;



         if ($sect ne "") {
			print "ARRL Section Found: ",$sect,"\n";
			if (($sect eq "EWA") or ($sect eq "WWA")) {
		      $is_wa = 1;
		    } else {
			$is_wa = 0;
   		    }
		}
	  }

   	  if ( (substr($qline,0,3) eq "QSO") || 
		   (($creator eq 'GENLOG') && (!($qline =~ /\:/))) )      # special case whacky GENLOG
								{
		 if ($creator eq '') {
			print "PROBLEM - NO LOGGING PROGRAM SPECIFIED AS CREATOR OF LOG - GUESSING\n";
			$creator="GUESS";
		 }

	     $total_q++;
		 # remove spaces from the line, split into fields
		 my @allfields;
		 my $sline=$qline;
		 $sline =~ s/\s+/ /g;
		 @allfields = split / /,$sline;
	     #$mode = substr($qline,11,2);
         #$band = substr($qline,5,5); 

		 $mode = $allfields[2];
	     $band = $allfields[1];
         # print "Mode: $mode Band: $band \n";
         $band = int($band / 1000);
		 GETFIELDS: {
			 # these are the defaults... 
	         $wrkd = substr($qline,$wrked_offset,$wrked_len);
    	     $wrkd =~ s/\s//g; # get rid of spaces
        	 $rexch = substr($qline,$exch_offset,$exch_len);
			 $sexch = substr($qline,$sent_offset,$sent_len);

		     if ($creator eq 'GENLOG') { # UGH - specify we only take cabrillo next time
				 $mode = substr($qline,6,2);
			 if ($mode eq 'RT') { $mode = 'RY'; }  
        		 $band = substr($qline,0,5);
	        	 $band = int(300/$band);
				 last GETFIELDS;
		 	 }
     		 if ($creator eq 'GUESS') { # we could make this smarter in the future
				 if ($iam ne $allfields[5]) {
					die "Couldn't guess the QSO line format\n";
				 }

				 if ($allfields[0] eq 'QSO:') {
					$band = $allfields[1];
		            $band = int($band / 1000);
				 } 
				 if ($allfields[0] =~ m/(\d+)m/ ) { # match 20m 40m 80m etc
				    $band=$1;	        	 
					$band = int(300/$band);
				 }
				 $wrkd = $allfields[8];
				 $rexch = $allfields[10];
				 $sexch = $allfields[7];
				 last GETFIELDS;
			 }
		     if ($creator eq 'TR') { # TR Log post - inconsistent column 
				 $wrkd = $allfields[8];
				 $rexch = $allfields[11];
				 if ($rexch eq '') {
                     $rexch = $allfields[10];
				  }
				 $sexch = $allfields[7];
				 last GETFIELDS;
			}
		 } # GETFIELDS
		 # print "Worked [$wrked_offset][$wrked_len]",$wrkd;
		 #print "exch [$exch_offset][$exch_len]",$rexch;
		 $sexch =~ s/\s+$//;	
		 $sexch =~ s/^\s+//;	
		 # print "sent exch [$sent_offset][$sent_len][",$sexch,"]\n";
         $SENT_EXCHANGE{$sexch}++;
		 if ('N1MM' eq $creator) {
	         $rexch =~ s/^\s*\d+\s+// ;   # remove any numbers - bug in N1MM
		 }
		 if ('TR' eq $creator) {
			 $rexch =~ s/(\d+\s+)+// ; # remove 59 or 599 
		 }
         $rexch =~ s/^\s+//; # get rid of spaces at beginning
		 #print "exch [$exch_offset][$exch_len]",$rexch;
		 $rexch =~ s/^(\S*)\s+.*/$1/; # if we have a space and more stuff, remove the end stuff ('ISL 4' -> 'ISL ')
		 #print "exch [$exch_offset][$exch_len]",$rexch;
         $rexch =~ s/\s+(\S*)\s+/$1/ ;  
         $rexch =~ s/\s//g; # get rid of spaces anywhere else
		 #print "exch [$exch_offset][$exch_len] ",$rexch,"\n";
         $rexch = substr($rexch,0,4); # limit length to four

		 SCORETYPE: {
		 if ($is_wa < 0) {
			print "\nPROBLEM - LOCATION OF STATION NOT SPECIFIED - \n";
			if ($sexch ne "") {
			  print "***** Looking at exchange to determine location\n";
			  if ($sexch eq "DX") {
				 print "***** Found DX as exchange, using NON-WA\n\n";
				 $is_wa = 0;
				 last SCORETYPE;
			  }
   			  if (defined($COUNTY{$sexch})) {
				 print "***** Found $sexch as Washington county, using WA\n\n";
				$is_wa = 1;
				last SCORETYPE;
			  } 
			  if (defined($STATEPROV{$sexch})) {
				print "*****  Found $sexch as State/Province, using NON-WA\n\n";
				$is_wa = 0;
				last SCORETYPE;
			  }
			  if (defined($DXCC_ENTITY{$sexch})) {
				print "***** Found $sexch as DXCC entity, using NON-WA\n\n";
				$is_wa = 0;
				last SCORETYPE;
			  }
		    } else {
				printf "***** No Sent exchange found, using WA by default\n";
				$is_wa = 1;
				last SCORETYPE;
			}     
		 }
		 } # SCORETYPE
         # use the call / band / mode / county to determine whether a duplicate
	 # 2008 - Normalize the mode
	 # print ("MODE $mode - ".normalize_mode($mode));
	 $mode = normalize_mode($mode);
	     $dupeindex = $wrkd.$band.$mode.$rexch;
		 if ($debug_scoring) { print "$wrkd\t$band\t$mode\t$rexch\n"; }
		 # only use the sent exchange if we have a field defined for it
		 if (defined($sent_offset)) { $dupeindex .= $sexch; }
		 $ISADUPE{$dupeindex}++;
         if ($ISADUPE{$dupeindex} > 1 ) {
			$dupecnt +=1;
			print "Dupe - $wrkd $band $mode $rexch\n";
	     } else {
			# score it
            # if washington, wa + states + dx are mults
            # if non-washington, only washington counties

            $modeqcnt{$mode}++;
			
			# print $wrkd,"\n";
			# record that we worked BONUS_STATION
            if ($wrkd eq $BONUS_STATION) {
			   if ($debug_scoring) { print "\t\t\t\tWorked $BONUS_STATION - mode: $mode\n"; }
			   $BONUS{$mode}++;
			}

			if (defined($COUNTY{$rexch})) {
				if ($debug_scoring) {
					if ($cntymult{$COUNTY{$rexch}} == 0) {
						print "\t\t\t\tnew county mult: ",$COUNTY{$rexch},"\n";
					}
				}
				$cntymult{$COUNTY{$rexch}}++;
			} else { 
                #
                # TODO - Match 'other' mults against a list of possible mults here...
			    # right now, just count anything...
                #
				# print "Other mult  = [$rexch]\n";
				# score other entities...
				 
				if (($rexch eq 'WA') || (!defined($DXCC_ENTITY{$rexch}) && !(defined($STATEPROV{$rexch})))) {
					print "Suspect exchange $rexch for QSO:\n",$qline,"\n";
				} else {
				  if ($is_wa) {
					# handle dx entity..
					$om = get_dxcc_entity($wrkd); 
					# print "$wrkd is from $om, gave [$rexch]\n";
					# removed VE from first clause
					if (($om eq "VE") || ($om eq 'K') || ($om eq 'KH6') || ($om eq 'KL')) {
						if (defined($STATEPROV{$rexch})) {
							if ($debug_scoring) {
								if ($statemult{$STATEPROV{$rexch}} == 0) {
									print "\t\t\t\tnew state/prov mult: ",$STATEPROV{$rexch},"\n";
								}	
							}
		 					$statemult{$rexch}++;
    	                } else { print "Invalid State or Province - $rexch - QSO:\n",$qline,"\n"; }
				    } else {
					    # todo - accept 'dx' here...
						if ($om eq get_dxcc_entity($rexch)) {
							if ($debug_scoring) {
								if ($dxmult{$om} == 0) {
									print "\t\t\t\tnew DX mult: ",$om,"\n";
								}	
							}
		 					$dxmult{$om}++;
						} else {
                          if ('DX' eq $rexch) {
						    print "Corrected 'DX' to ",get_dxcc_entity($wrkd)," - QSO:\n",$qline,"\n";
			 				$dxmult{get_dxcc_entity($wrkd)}++;
						  } else {
							print "DX Callsign [$wrkd] doesn't match exchange - $om vs $rexch - QSO:\n",$qline,"\n"; 
                            }
                         }
                    }
            	  }
				}
			}
		  }
        }
		$idx++;
	  }
      # show what we have
      $totpoints = 0;
      # calc bonus pts
	  foreach $i (@W7DX_BONUS_MODES) {
		# print "BONUS $i ";
		$bonus_pts+=500 if defined($BONUS{$i});
	  }
      print "\nSummary for $iam\nMode\t\tQs \tPoints\n";
	  foreach $i (keys %modeqcnt) {
       	printf "%s\t%6d\t%10d\n",$i,$modeqcnt{$i},$modeqcnt{$i} * $QPT{$i};
		$totpoints += $modeqcnt{$i} * $QPT{$i};
	  }
      printf "\t\t===============\nQSO Points\t%10d\n\n",$totpoints;
      # show the mult counts

      $wa_cnty = scalar (keys %cntymult);
      print "Sent Exchange: ";
          foreach $i (sort (keys %SENT_EXCHANGE)) {
			print $i," ";
       	  }
	  print "\n";
	  printf "WA Counties:\t%10d\n",$wa_cnty;
      if ($is_wa) {
          $state_cnt = 0; 
	      $dx_cnt = 0;
          $state_cnt = scalar(keys %statemult);
      	  printf "\nSt/Prov:\t%10d\n",$state_cnt;
          foreach $i (sort (keys %statemult)) {
			print $i," ";

       	  }
		  print "\n";
          $dx_cnt = scalar(keys %dxmult);
	      printf "DX:\t\t%10d\n",$dx_cnt;
		  foreach $i (sort (keys %dxmult)) {
			print $i," ";
       	  }
          print "\n";

	  }
      printf "BONUS $BONUS_STATION:\t%10d\n",$bonus_pts;
      $calc_score = $totpoints * ($dx_cnt+$state_cnt + $wa_cnty) + $bonus_pts;
	  printf "\nCLAIMED SCORE\t%10d\t\tCALCULATED SCORE  :\t%10d\n",$claimed_score,$calc_score;
      #foreach $i ('CALLSIGN','ARRL-SECTION','CATEGORY','CLAIMED-SCORE','CREATED-BY','OPERATORS','NAME', 'ADDRESS',
	  #			  'CALCD-SCORE','CW-Q','PH-Q','DIG-Q','WA-COUNTIES','STATES','DX','W7DX-PTS') {
      #   print $i,",";
	  #}
	  #print "\n";
      open (SCF,">>$SCOREFILE") or die "Can't write to score record file";
      foreach $i ('CALLSIGN','ARRL-SECTION','CATEGORY','CLAIMED-SCORE','CREATED-BY','OPERATORS','NAME', 'ADDRESS') {
         print SCF '"',$LOGHEADER{$i},'",';
	  }

	  my $allsentexch = "";
      foreach $i (sort (keys %SENT_EXCHANGE)) {
			$allsentexch .= ($i . " ");
       	  }
      print SCF sprintf "%d,%d,%d,%d,%d,%d,%d,%d,%d,\"%s\",\"%s\"",
			$calc_score,$modeqcnt{'CW'},
            $modeqcnt{'PH'},$modeqcnt{'DG'}+$modeqcnt{'RY'}+$modeqcnt{'PS'},$wa_cnty,$state_cnt,$dx_cnt,
			$bonus_pts,$dupecnt,$filename,$allsentexch;

	  print SCF "\n";
}

# read ct.dat file for DXCC entity information
# this is used to find the right DXCC info for say OH2BH/W3...
sub load_ct_file {
	my @ap;
	#local $/ = "\r\n";
	my $dxcc_prefix; my $alias_prefixes; my $i;
	open (CT,"<$CTFILE") or die "Can't find CT master file";
	while (<CT>) {
	  $_ =~ s/\r?\n$// ;
	  # chomp ;
	  if ($debug_level > 8) { print $_ . "\n";}
	  $dxcc_prefix = substr($_,69,7);
	  $dxcc_prefix =~ s/\://;
	  if ($debug_level > 5) { print $dxcc_prefix," = \n"; }
          $DXCC_ENTITY{$dxcc_prefix} = $dxcc_prefix;
	  do {
	    $alias_prefixes = <CT> ;
	        $alias_prefixes =~ s/\r?\n$// ;
		# chomp $alias_prefixes;
            if ($debug_level > 8) { print $alias_prefixes . "\n";}
	    @ap = split (/[,;]/, $alias_prefixes);
	    foreach $i  (@ap) {
		  $i =~ s/\s//g; 
		  $i =~ s/\(\d+\)//g;
		  $i =~ s/\[\d+\]//g;
		  if ($debug_level > 8) { print $i," "; }
		  $DXCC_ENTITY{$i}=$dxcc_prefix;
	    }
	 } while (!($alias_prefixes=~ m/\;$/s )) ;
	  if ($debug_level > 5) { print "\n";}
	}
	close ZL;   
}
# get the dxcc entity for a call. Handle prefixes like OH/W2BH but not suffixes like w4my/3
sub get_dxcc_entity {
	my $debug_dxcc;
	my $callsign; my $o_callsign; my $dxe;
	$debug_dxcc = 0;
	($callsign) =  @_;
	if ($debug_dxcc) { print "get_dxcc_entity:looking up $callsign\n"; }
	# handle the Entity prefix case...
	if ($callsign =~ /(.*)\/(.*)/ ) {
	  # we have a prefix
	  my $part1 = $1;
	  my $part2 = $2;
	  if ($debug_dxcc) { print "Callsign is suffixed $1/$2\n"; }
      my $prefix = $part1;
	  my $pp;
	  if (length($part1) > length($part2)) { # try to determine which is a country specifier
		$pp = uc($part2);
	    if ($debug_dxcc) { print "Suffix $pp is smaller.. checking special cases.\n"; }
		# valid: USCALLSIGN/VE1
        # not valid: VE1/USCALLSIGN
        # valid: VP5/USCALLSIGN
        # not valid: USCALLSIGN/VP5
		HANDLEPREFIX: {
			# the default case - prefix precedes the call
			if (($pp eq 'M') || ($pp eq 'MM')) { if ($debug_dxcc) { print ("Mobile\n"); } last HANDLEPREFIX; }
			if ($pp =~ /^\d$/) { $prefix='W'.$pp; last HANDLEPREFIX; } # special case us calls in other area
			# 
			if (get_dxcc_entity($part2) eq 'XE') { $prefix=$part2; last HANDLEPREFIX; } 

			if (get_dxcc_entity($part1) =~ m/^K/) { # match US and possessions 
				my $suffix = get_dxcc_entity($part2);
				if ($debug_dxcc) {print "Suffix entity is $suffix\n"; }
			    if ($suffix eq 'VE') { $prefix = $suffix; last HANDLEPREFIX;}
				if ($suffix =~ m/^K/) { $prefix = $suffix; last HANDLEPREFIX;}
			}
		}
	    if ($debug_dxcc) { print "entity is $prefix\n"; }
	  }
	  if ($debug_dxcc) { print "2:Looking up $prefix\n"; }
      if (defined($DXCC_ENTITY{$prefix})) {return $DXCC_ENTITY{$prefix}; }
	  # hmm...
      $callsign = $prefix;
    }
    # do a longer search...
    if ($debug_dxcc) { print "Doing a longer search on $callsign\n"; }
    $o_callsign = $callsign;
    while (length($callsign)) {
	  if ($debug_dxcc) { print "Iterate: $callsign\n"; }
	  $dxe = $DXCC_ENTITY{$callsign};
	  if (defined($dxe)) { 
		if ($debug_dxcc) {print "Found entity: $dxe\n"; }
		if (($dxe eq 'KG4') && (length($o_callsign)>5)) { return "K"; } # special case for guantanamo
		return $dxe;
      }
	  # only keep searching if callsign only has alpha+numbers in it...
	  $callsign = substr($callsign,0,length($callsign)-1);
    }
	return undef;
}

sub load_log {
	my $logfile;my $idx;
	$logfile=shift @_;
	#
    undef @LOG;
	if (! (open LFILE,"<$logfile") ) {
	   print("Can't open log file $logfile\n");
	   return 0;
	}
	$idx = 0; 
    while(<LFILE>) {
	  $_ =~ s/\r?\n$// ;
	  #chomp;
	  
	  $LOG[$idx++] = uc;
	}
	close LFILE;
	return $idx;
}

sub load_cntylist {
	my @cl;
	my  $i;
	open (ZL,"<$COUNTYLIST") or die "Can't find the list of counties";
	while (<ZL>) {
	  $_ =~ s/\r?\n$// ;
	  #chomp ;
	  # handle abbreviations
	  @cl = split " ";
	  foreach $i (@cl) {
			# print "County $i $cl[0]\n";
			$COUNTY{$i} = $cl[0];
	  }
	  #      $COUNTY{$_}=$_;	  
	}
	close ZL;
}

sub load_states_and_provinces {
	my @tokens;
	open (ZL,"<$STATESPROVS") or die "Can't find the list of states and provinces";
	while (<ZL>) {  # read the section of Type=50S8P Subtype= from file. ADD KL AK line to this file! 
	  $_ =~ s/\r?\n$// ;
        # chomp;
       last if (/^Type=\s*50S8P/) ;
	}
    if (!defined($_)) { die "Can't find the section we need"; }
	while (<ZL>) {
	  $_ =~ s/\r?\n$// ;
	  #chomp;
       last if ( /^Type=/) ; # done reading stuff in
	   next if ( /^'/ ) ; # skip commented lines
       @tokens = split / /;
	   # print $#tokens;
       if ($#tokens == 1 ) {
		   #print "Adding alias for ",$tokens[1]," ",$tokens[0],"\n";
		  $STATEPROV{$tokens[0]} = $tokens[1];
		}
	   if ($#tokens == 0 ) {
		  # print "Adding ",$tokens[0],"\n";
	      $STATEPROV{$tokens[0]} = $tokens[0];
	   }
	}
	close ZL;
}
sub load_zonelist {
	my $state; my $zone;
	open (ZL,"<$ZONELIST") or die "Can't find the list of zones";
	while (<ZL>) {
	  $_ =~ s/\r?\n$// ;
	  # chomp ;
	  s/.*\((\S\S)\).* CQ\s+(\d+)/$1 $2/;
	  $state = $1;
      $zone = $2 + 0;
	  # print "$state $zone\n";
      $STZONE{$state}=$zone;	  
	}
	close ZL;
}
    warn("Loading states and provinces") if $debug_level>5;
    load_states_and_provinces();
    warn("Loading ct file") if $debug_level>5;
    load_ct_file();
    warn("Loading zonelist file") if $debug_level>5;
    load_zonelist();
    warn("Loading zonelist file") if $debug_level>5;
    load_cntylist();
    warn("Starting log run") if $debug_level>5;

    my $lc; my @fg; my $ff;
    $lc = $#ARGV;
    while($lc >= 0){
   	  $logfile = $ARGV[$lc];
          @fg = glob $logfile;
	  # open LOG,"<$logfile" or die "Can't open log file [$logfile]\n";
	  for $ff (@fg) {
		 print "\n---------------------------------------------------------------------------\n";
             print "Opening ",$ff,"\n";
             load_log($ff);
             score_log($ff);
	  }
	  $lc--;
      }
