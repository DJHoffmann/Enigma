  Enigma.py

  David Hoffmann
  2018
  GNU General Public License

  Fun Python code to crack the WW2 German Enigma code, using similar method to the mechanical Turing Bombe 
  machines, adapted & modernised to run on current hardware.

  Relies on a guessable crib word at the beginning of each message (eg. WETTERVORHERSAGEBISKAYA - 
  German for weather report in the Biscay region, a regularly sent and intercepted message).
  This followed the standard three letter message key (encrypted according to the universal day key).

  From a single intercepted enciphered message the code obtains the enigma rotor types & positions, 
  initial rotor settings and message key, even when chosen in line with proper procedure (unguessable). 
  Note that for the slow rotor only the offset between initial orientation and ring setting is found, 
  as the encryption is invariant to any initial rotation with this fixed offset.

  Decryption of a second intercepted enciphered message, with a different message key but otherwise 
  identical settings (no less general as >1 would certainly be intercepted per day!) allows for 
  fast calculation of the day key: the final piece of the puzzle necessary for easy decryption of all 
  messages that day.

  I intend to write a more comprehensive explanation of the method used. Although it is based on the 
  Turing Bomb machines, their workings are not at all well described in any literature that I could find.
  A good deal of thought and retreading of old steps was required, although fortunately I had the 
  advantage of knowing that in this approach a solution was there be found!

  The code typically takes around 1-10 minutes on an average laptop for the first decription, dependent
  on initial enigma settings. We have no choice but to take a fixed started point for the search, so if 
  the slow rotor starts at the opposite end of the (wrapped) alphabet, then we will take much longer 
  than at a letter or two ahead.  The second decription for the day key will take around 30 seconds.

  Chance of slow rotor advance during crib is ~ crib length / 676, so for crib tests remove the possibility
  of slow rotor advance. The code will fail if this does happen, but if slow rotor advance is permitted the 
  code would fail 25 times out of 26 when "slow rotor offset" corresponds to a slow rotor notch value
  (a far more common occurrence).
