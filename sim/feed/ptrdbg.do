onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/DUT/dly_ld
add wave -noupdate /tb/DUT/ld_ptrs
add wave -noupdate -radix decimal /tb/DUT/nxt_len
add wave -noupdate /tb/DUT/que_ptr
add wave -noupdate /tb/DUT/rd_ptr
add wave -noupdate /tb/DUT/eom_ptr
add wave -noupdate /tb/DUT/eom_in_old
add wave -noupdate -expand /tb/DUT/old_beat
add wave -noupdate -expand /tb/DUT/new_beat
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {970807 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 335
configure wave -valuecolwidth 277
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {761461 ps} {1039039 ps}
