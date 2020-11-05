
restart -f
delete wave *
transcript file log_rab_test.log
onbreak {resume}
view objects
view locals
view source
view wave 

do ./wave.do

