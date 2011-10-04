module type OUTCHAN = sig
  val out: out_channel
  val directory_name: string
  val file_name: string
end

